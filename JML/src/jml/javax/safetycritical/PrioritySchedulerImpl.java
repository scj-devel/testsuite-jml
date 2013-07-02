package jml.javax.safetycritical;

import jml.vm.Process;
import jml.vm.Scheduler;


final class PrioritySchedulerImpl implements Scheduler {

	@Override
	public Process getNextProcess() {
		ScjProcess scjProcess = PriorityScheduler.instance().move();

		if (scjProcess != null) {
			return scjProcess.process;
		}
		PriorityScheduler.instance().stop(PriorityScheduler.instance().current.process);
		return null;
	}

}
