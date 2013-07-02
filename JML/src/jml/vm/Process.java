package jml.vm;

import icecaptools.IcecapCompileMe;

public class Process {
	private Runnable logic;
	private int[] stack;
	private ProcessExecutor processExecuter;
	private SP sp;

	@IcecapCompileMe
	public Process(Runnable logic, int[] stack) {
		this.logic = logic;
		this.stack = stack;

		processExecuter = new ProcessExecutor(this);
		switch (Architecture.architecture) {
		case Architecture.X86_64:
			sp = new X86_64SP();
			break;
		case Architecture.CR16_C:
		case Architecture.X86_32:
			sp = new X86_32SP();
			break;
		}
	}

	@IcecapCompileMe
	public void transferTo(Process nextProcess) {
		transfer(this, nextProcess);
	}

	public final void initialize() {
		executeWithStack(processExecuter, stack);
	}

	private static native void transfer(Process currentProcess, Process nextProcess);

	public static native void executeWithStack(Runnable runnable, int[] schedulerStack);
	
	private static class ProcessExecutor implements Runnable {
		private Process thisProcess;
		private boolean isStarted;
		
		ProcessExecutor(Process thisProcess) {
			this.thisProcess = thisProcess;
		}

		@Override
		@IcecapCompileMe
		public void run() {
			isStarted = false;
			thisProcess.transferTo(thisProcess);
			if (!isStarted) {
				isStarted = true;
			} else {
				thisProcess.logic.run();
				jml.vm.ClockInterruptHandler.instance.yield();
			}
		}
	}
	
	private static abstract class SP {

	}
	
	private static class X86_32SP extends SP {
		@SuppressWarnings("unused")
		public int sp;
	}
	
	private static class X86_64SP extends SP {
		@SuppressWarnings("unused")
		public long sp;
	}
}
