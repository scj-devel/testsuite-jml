package jml.javax.safetycritical;

import jml.vm.InterruptHandler;

import icecaptools.IcecapCompileMe;

final class Monitor extends jml.vm.Monitor {
	private int ceiling;
	private int synchCounter;
	private int priority;
	private ManagedEventHandler owner;
	private InterruptHandler clock;
	
	public Monitor(int ceiling) {
		this.ceiling = ceiling;
		clock = jml.vm.ClockInterruptHandler.instance;
	}

	@IcecapCompileMe
	@Override
	public void lock() {
		clock.disable();
		ManagedEventHandler handler = PriorityScheduler.instance().current.target;
		if (owner == null) {
			owner = handler;
		}

		if (owner == handler) {
			synchCounter++;
			if (synchCounter == 1) {
				priority = handler.priority.getPriority();
				handler.priority.setPriority(max(priority, ceiling) + 1);
			}
		} else {
			clock.enable();
			throw new IllegalMonitorStateException("Not owner on entry");
		}
		clock.enable();
	}

	@IcecapCompileMe
	@Override
	public void unlock() {
		clock.disable();
		ManagedEventHandler handler = PriorityScheduler.instance().current.target;
		if (owner == handler) {
			synchCounter--;
			if (synchCounter == 0) {
				owner = null;
				handler.priority.setPriority(priority);
				clock.enable();
				clock.handle();
			}
		}
		else
		{
			clock.enable();
			throw new IllegalMonitorStateException("Not owner on exit");
		}
	}

	private static int max(int x, int y) {
		if (x > y)
			return x;
		else
			return y;
	}
}
