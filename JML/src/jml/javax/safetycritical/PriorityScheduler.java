/**************************************************************************
 * File name  : PriorityScheduler.java
 * 
 * This file is part of our SCJ Level 0 and Level 1 implementation, 
 * based on SCJ Draft, Version 0.79. 16 May 2011.
 *
 * It is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as  
 * published by the Free Software Foundation, either version 3 of the 
 * License, or (at your option) any later version.
 *
 * This SCJ Level 0 and Level 1 implementation is distributed in the hope 
 * that it will be useful, but WITHOUT ANY WARRANTY; without even the  
 * implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  
 * See the GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this SCJ Level 0 and Level 1 implementation.  
 * If not, see <http://www.gnu.org/licenses/>.
 *
 * Copyright 2012 
 * @authors  Anders P. Ravn, Aalborg University, DK
 *           Stephan E. Korsholm and Hans S&oslash;ndergaard, 
 *             VIA University College, DK
 *   
 * Description: 
 * 
 * Revision history:
 *   date   init  comment
 *
 *************************************************************************/
package jml.javax.safetycritical;

//import icecaptools.IcecapCompileMe;

import jml.javax.safetycritical.annotate.Level;
import jml.javax.safetycritical.annotate.SCJAllowed;
import jml.javax.scj.util.Const;
import jml.javax.scj.util.Priorities;

import jml.vm.ClockInterruptHandler;

/**
 * This class represents the priority-based scheduler for Level 1 and 2. <br>
 * The only access to the priority scheduler is for obtaining the software
 * priorities.
 * 
 * @version 1.0; - May 2012
 * 
 * @author Anders P. Ravn, Aalborg University, <A
 *         HREF="mailto:apr@cs.aau.dk">apr@cs.aau.dk</A>, <br>
 *         Hans S&oslash;ndergaard, VIA University College, Denmark, <A
 *         HREF="mailto:hso@viauc.dk">hso@viauc.dk</A>
 * 
 * @scjComment - SCJ issue: No <code>javax.realtime.PriorityScheduler</code>
 *             class.
 */
@SCJAllowed(Level.LEVEL_1)
public class PriorityScheduler extends Scheduler
{
	PriorityFrame pFrame;

	ScjProcess current;
	PrioritySchedulerImpl prioritySchedulerImpl;

	Clock rtClock;
	AbsoluteTime now;

	int count = 0; // internal use

	private static PriorityScheduler scheduler; 
	
	/**
	 * 
	 * @return The priority scheduler.
	 */
	/*@ // implementation specification 
      requires true;
      ensures \result == PriorityScheduler.scheduler;
    @*/
	@SCJAllowed(Level.LEVEL_1)
	public static PriorityScheduler instance() {
		if (scheduler == null) {
			scheduler = new PriorityScheduler();
		}
		return scheduler;
	}

	public PriorityScheduler() {  // only public for test; else private
		int[] schedulerStack = new int[Const.PRIORITY_SCHEDULER_STACK_SIZE];

		this.pFrame = new PriorityFrame(Const.DEFAULT_PRIORITY_QUEUE_SIZE);
		this.prioritySchedulerImpl = new PrioritySchedulerImpl();

		ClockInterruptHandler.initialize(this.prioritySchedulerImpl, schedulerStack);

		this.rtClock = Clock.getRealtimeClock();
		this.now = new AbsoluteTime(this.rtClock);
		rtClock.getTime(this.now);
	}

	void add(ManagedEventHandler handler, int[] stack) {
		ScjProcess process = new ScjProcess(handler, stack);
		if (handler instanceof MissionSequencer) {
			process.index = -2;
			MissionSequencer.missSeqProcess = process;
		} else {
			process.index = HandlerSet.getHandlerSet().indexOf(handler);
		}
		pFrame.addProcess(process);
	}

	void start() {
		// put idle process in readyQueue
		pFrame.readyQueue.insert(ScjProcess.createIdleProcess());
		current = pFrame.readyQueue.extractMax();
		super.start();
	}

	void release(AperiodicEventHandler handler) {
		// see AperiodicEventHandler, where release is called
		ClockInterruptHandler.instance.disable();
		if (handler.process.state == ScjProcess.State.EXECUTING) {
			; // do nothing, - is already running
		}

		else if (handler.process.state == ScjProcess.State.BLOCKED) {
			handler.process.state = ScjProcess.State.READY;
			pFrame.readyQueue.insert(handler.process);
		} else {
			; // it is already ready
		}
		ClockInterruptHandler.instance.enable();
	}

	//  @IcecapCompileMe
	ScjProcess move() {
		if (current == ScjProcess.idleProcess) {
			pFrame.readyQueue.insert(current);
		}

		// periodic handlers
		else if (current.target instanceof PeriodicEventHandler) {
			if (current.state == ScjProcess.State.HANDLED) {
				// finished executing handleAsyncEvent

				if (HandlerSet.mission.terminationPending()) {
					HandlerSet.getHandlerSet().removeHandler(current.target);

					current.state = ScjProcess.State.TERMINATED;
				} else {
					current.state = ScjProcess.State.SLEEPING;
					current.start();
					pFrame.sleepingQueue.insert(current);
					// devices.Console.println("On sQueue: " + current);
				}
			} else {
				// handler was preempted
				current.state = ScjProcess.State.READY;
				pFrame.readyQueue.insert(current);
				// devices.Console.println("Preempted; on rQueue: " + current);
			}
		}

		else if (current.target instanceof MissionSequencer) {
			if (current.state == ScjProcess.State.HANDLED) {
				// missionSequencer terminates

				current.target.cleanUp();
				current.state = ScjProcess.State.TERMINATED;
			} else {
				// handler was preempted
				current.state = ScjProcess.State.READY;
				pFrame.readyQueue.insert(current);
			}
		}

		else if (current.target instanceof AperiodicEventHandler) {
			if (current.state == ScjProcess.State.HANDLED) {
				// AperiodicEventHandler finished handling
				((AperiodicEventHandler) current.target).fireCount--;
				// devices.Console.println("PrSch.move: apevh finished, fireCount: "
				// + ((AperiodicEventHandler)current.target).fireCount);

				// if (HandlerSet.mission.terminationPending()) //
				// sequenceTerminationPending())
				if (HandlerSet.mission.terminationPending()) {
					HandlerSet.getHandlerSet().removeHandler(current.target);

					// devices.Console.println("PrSch.move: apevh terminate: " +
					// HandlerSet.getHandlerSet().handlerCount);

					// remove the rest of aperiodic handlers
					HandlerSet.getHandlerSet().removeAperiodicHandlers();

					current.state = ScjProcess.State.TERMINATED;
				} else if (((AperiodicEventHandler) current.target).fireCount == 0)
					current.state = ScjProcess.State.BLOCKED;
				else { // re-activate
					current.state = ScjProcess.State.READY;
					pFrame.readyQueue.insert(current);
				}
			} else {
				// handler was preempted

				current.state = ScjProcess.State.READY;
				pFrame.readyQueue.insert(current);
			}
		} else {
			throw new IllegalArgumentException("PriorityScheduler.move: UPS: another handler??");
		}

		// Move processes from sleepingQueue to readyQueue
		ScjProcess process = pFrame.sleepingQueue.minimum();
		// devices.Console.println("sleepingQueue.minimum:  " + process);

		rtClock.getTime(now);

		while (process != null && process.next.compareTo(now) <= 0) {
			process.state = ScjProcess.State.READY;
			ScjProcess t = pFrame.sleepingQueue.extractMin();

			pFrame.readyQueue.insert(t);

			// look at "next" process in sleeping queue with smallest
			// activationTime
			process = pFrame.sleepingQueue.minimum();
		}

		// get next process from readyQueue
		ScjProcess nextProcess = pFrame.readyQueue.extractMax();
		nextProcess.state = ScjProcess.State.EXECUTING;
		current = nextProcess;

		if ((current == ScjProcess.idleProcess) && (pFrame.sleepingQueue.heapSize == 0)) {
			current.target.cleanUp();
			return null;
		} else {
			return nextProcess;
		}
	}

	/**
	 * 
	 * @return The maximum software real-time priority supported by this
	 *         scheduler.
	 */
	/*@ // implementation specification 
      requires true; 
      assignable \nothing;
      ensures \result == Priorities.MAX_PRIORITY;
    @*/
	public int getMaxPriority() {
		return Priorities.MAX_PRIORITY;
	}

	/**
	 * 
	 * @return The minimum software real-time priority supported by this
	 *         scheduler.
	 */
	/*@ // implementation specification 
      requires true; 
      assignable \nothing;
      ensures \result == Priorities.MIN_PRIORITY;
    @*/
	public int getMinPriority() {
		return Priorities.MIN_PRIORITY;
	}

//	/**
//	 * 
//	 * @return The normal software real-time priority supported by this
//	 *         scheduler.
//	 */
//	/*@ // implementation specification 
//      requires true; 
//      assignable \nothing;
//      ensures \result == Priorities.NORM_PRIORITY;
//    @*/
//	public int getNormPriority() {
//		return Priorities.NORM_PRIORITY;
//	}

	/**
	 * 
	 * @return The maximum hardware real-time priority supported by this
	 *         scheduler.
	 */
	/*@ // implementation specification 
      requires true; 
      assignable \nothing;
      ensures \result == Priorities.MAX_HARDWARE_PRIORITY;
    @*/
	public int getMaxHardwarePriority() {
		return Priorities.MAX_HARDWARE_PRIORITY;
	}

	/**
	 * 
	 * @return The minimum hardware real-time priority supported by this
	 *         scheduler.
	 */
	/*@ // implementation specification 
      requires true; 
      assignable \nothing;
      ensures \result == Priorities.MIN_HARDWARE_PRIORITY;
    @*/
	public int getMinHardwarePriority() {
		return Priorities.MIN_HARDWARE_PRIORITY;
	}
}
