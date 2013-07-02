package jml.vm;

import icecaptools.IcecapCVar;
import icecaptools.IcecapCompileMe;
import devices.CR16C.KT4585.CR16CInterruptDispatcher;
import devices.i86.I86InterruptDispatcher;

/* Add setScheduler(Scheduler sch)  */
public class ClockInterruptHandler implements InterruptHandler {
	private Process currentProcess;
	private jml.vm.Scheduler scheduler;

	@SuppressWarnings("unused")
	@IcecapCVar
	private static boolean hvmClockReady;

	private class HandlerExecutor implements Runnable {
		@Override
		public void run() {
			while (true) {
				currentProcess = (Process) scheduler.getNextProcess();
				enable();
				handlerProcess.transferTo(currentProcess);
			}
		}
	}

	private Process handlerProcess;

	private ClockInterruptHandler(Scheduler scheduler, int[] stack) {
		this.scheduler = scheduler;
		handlerProcess = new jml.vm.Process(new HandlerExecutor(), stack);
		handlerProcess.initialize();
	}

	@IcecapCompileMe
	@Override
	public void handle() {
		disable();
		currentProcess.transferTo(handlerProcess);
	}

	@IcecapCompileMe
	@Override
	public void disable() {
		hvmClockReady = false;

	}

	@IcecapCompileMe
	@Override
	public void enable() {
		hvmClockReady = true;
	}

	public static ClockInterruptHandler instance;

	@IcecapCompileMe
	public static void initialize(Scheduler scheduler, int[] stack) {
		switch (Architecture.architecture) {
		case Architecture.X86_64:
		case Architecture.X86_32:
			I86InterruptDispatcher.init();
			break;
		case Architecture.CR16_C:
			CR16CInterruptDispatcher.init();
			break;
		}
		instance = new ClockInterruptHandler(scheduler, stack);
	}

	public void yield() {
		handle();
	}

	@Override
	public void register() {
		InterruptDispatcher.registerHandler(this, InterruptDispatcher.HVM_CLOCK);
	}

	public void startClockHandler(Process process) {
		this.currentProcess = process;
	}
	
	public void setScheduler(Scheduler sch)
	{
		this.scheduler = sch;
	}
}