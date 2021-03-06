/**************************************************************************
 * File name  : MissionSequencer.java
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

import jml.javax.safetycritical.annotate.Level;
import jml.javax.safetycritical.annotate.Phase;
import jml.javax.safetycritical.annotate.SCJAllowed;
import jml.javax.safetycritical.annotate.SCJRestricted;

import jml.javax.scj.util.Priorities;

/**
 * A <code>MissionSequencer</code> runs a sequence of independent
 * <code>Mission</code>s.
 * 
 * @version 1.0; - May 2012
 * 
 * @author Anders P. Ravn, Aalborg University, <A
 *         HREF="mailto:apr@cs.aau.dk">apr@cs.aau.dk</A>, <br>
 *         Hans S&oslash;ndergaard, VIA University College, Denmark, <A
 *         HREF="mailto:hso@viauc.dk">hso@viauc.dk</A>
 * 
 * 
 * @scjComment - SCJ issue: Occurs sometimes as <code>MissionSequencer</code>,
 *             but most often as
 *             <code>MissionSequencer&lt;SpecificMission&gt;</code> ? <br>
 * 
 *             - SCJ issue: Why Level 2 only for the following two methods?
 *             <ul>
 *             <code>
 *     <li>public final void requestSequenceTermination() <br>
 *     <li>public final boolean sequenceTerminationPending() 
 *   </code>
 *             </ul>
 *             - SCJ issue: @SCJRestricted({INITIALIZATION}) is not a defined
 *             annotation.
 */
@SCJAllowed
public abstract class MissionSequencer/* <SpecificMission> */extends ManagedEventHandler {

	MissionMemory missionMemory;
	Mission currMission;

	interface State {
		public final static int START = 1;
		public final static int INITIALIZE = 2;
		public final static int EXECUTE = 3;
		public final static int CLEANUP = 4;
		public final static int TERMINATE = 5;
		public final static int END = 6;
	}

	int currState;
	boolean terminateSeq = false;

	static ScjProcess missSeqProcess = null;

	/*@ public invariant  
         Priorities.MIN_PRIORITY <= this.priority.getPriority() &&
         this.priority.getPriority() <= Priorities.MAX_PRIORITY;
    
    @*/


	/**
	 * Constructs a <code>MissionSequencer</code> to run at the priority and
	 * with the memory resources specified by its parameters.
	 */
	/*@ // implementation specification 
	    requires (priority != null) &&
        (Priorities.MIN_PRIORITY <= priority.getPriority() &&
           priority.getPriority() <= Priorities.MAX_PRIORITY); 
        // the above is the invariant of Priorities; necessary to put it here?
        // I our implementation, the priority must be smaller than the priorities
        // of the handlers in the mission (how can this be expressed?)
      requires storage  != null;         
      
      assignable this.priority;
      
      ensures true;
      
    @*/
	@SCJAllowed
	@SCJRestricted(Phase.INITIALIZE)
	public MissionSequencer(PriorityParameters priority, StorageParameters storage) {
		super(priority, null, storage);

		missionMemory = new MissionMemory((int) storage.configurationSizes[0]);

		currState = State.START;
		if (Launcher.level == 1) {
			PriorityScheduler.instance().add(this, new int[default_stack_size]);
		}
	}

	/**
	 * This method is declared final because the implementation is provided by
	 * the infrastructure of the SCJ implementation and shall not be overridden. <br>
	 * This method performs all of the activities that correspond to sequencing
	 * of <code>Mission</code>s by this <code>MissionSequencer</code>.
	 */
	/*@ // implementation specification 
      requires true; 
      assignable \nothing;
      ensures true; // ??
    @*/
	@SCJAllowed(Level.SUPPORT)
	public final void handleAsyncEvent() {
		do {
			// the main actions of the sequencer governed by currState
			switch (currState) {
			case State.START:
				currMission = /* (Mission) */getNextMission();

				if (currMission == null || terminateSeq) {
					terminateSeq = true;
					currState = State.TERMINATE;
				} else {
					currMission.missionTerminate = false;
					currState = State.INITIALIZE;
				}
				break;

			case State.INITIALIZE:
				currMission.setMissionSeq(this);
				missionMemory.enterToInitialize(currMission);

				currState = State.EXECUTE;
				break;

			case State.EXECUTE:
				missionMemory.enterToExecute(currMission);

				currState = State.CLEANUP;
				break;

			case State.CLEANUP:
				missionMemory.enterToCleanup(currMission);

				// privateMemory.resetMemoryArea(); // reset here? NO:
				// handleAsyncEvent continues

				currState = State.START;
				break;

			case State.TERMINATE:
				currState = State.END;
			default:
			}
		} while (currState < State.END);
	}

	/**
	 * This method is called by the infrastructure to select the next
	 * <code>Mission</code> to execute. <br>
	 * Prior to each invocation of <code>getNextMission</code> by the
	 * infrastructure, the infrastructure instantiates and enters a <code>
	 * MissionMemory</code>, initially sized to represent all available backing
	 * store.
	 * 
	 * @return The next <code>Mission</code> to run, or null if no further
	 *         <code>Mission</code>s are to run under the control of this
	 *         <code>MissionSequencer</code>.
	 */
	@SCJAllowed(Level.SUPPORT)
	protected abstract/* Specific */Mission getNextMission();

	/*@ requires true; 
      assignable \nothing;
      ensures true; // ??
    @*/
	public final void register() {
		super.register();
	}

	/**
	 * Invokes the currently running <code>Mission</code>'s <code>
	 * requestTermination</code> method. <br>
	 * Upon completion of the currently running <code>Mission</code>, this
	 * <code>MissionSequencer</code> returns without starting any additional
	 * missions.
	 * <p>
	 * Note that <code>requestSequenceTermination</code> does not force the
	 * sequence to terminate because the currently running <code>Mission</code>
	 * must voluntarily relinquish its resources.
	 * 
	 * @scjComment Why Level 2 only?
	 */
	/*@ requires true; 
      assignable \nothing;
      ensures true; // ??
    @*/
	@SCJAllowed
	public final void requestSequenceTermination() {
		terminateSeq = true;
		currMission.requestTermination();
	}

	/**
	 * Checks if the current <code>Mission</code> is trying to terminate.
	 * 
	 * @scjComment Why Level 2 only?
	 * 
	 * @return True if and only if this <code>MissionSequencer</code>'s
	 *         <code>requestSequenceTermination</code> method has been invoked.
	 */
	/*@ requires true; 
      assignable \nothing;
      ensures true; // ??
    @*/
	@SCJAllowed
	public final boolean sequenceTerminationPending() {
		return terminateSeq;
	}

	/*@ requires true; 
      assignable \nothing;
      ensures true; // ??
    @*/
	@Override
	public final void cleanUp() {
		super.cleanUp();
		missionMemory.removeArea();
	}
}
