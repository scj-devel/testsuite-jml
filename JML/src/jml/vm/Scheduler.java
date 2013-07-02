package jml.vm;

public interface Scheduler {
	public jml.vm.Process getNextProcess();
	
	/* TODO: void terminated(); */
}
