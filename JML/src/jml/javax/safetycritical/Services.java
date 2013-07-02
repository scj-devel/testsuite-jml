package jml.javax.safetycritical;

import jml.javax.safetycritical.annotate.Level;
import jml.javax.safetycritical.annotate.Phase;
import jml.javax.safetycritical.annotate.SCJAllowed;
import jml.javax.safetycritical.annotate.SCJRestricted;

@SCJAllowed
public class Services {

  /*@ 
    public behavior
      requires true;
      ensures \result == PriorityScheduler.instance().getMaxPriority();
    @*/
  @SCJAllowed(Level.LEVEL_1)
	public static int getDefaultCeiling() {
		return PriorityScheduler.instance().getMaxPriority();
	}

  /*@ 
    public behavior
      requires target != null;
      requires 
          (PriorityScheduler.instance().getMinPriority() <= ceiling && 
           ceiling <= PriorityScheduler.instance().getMaxPriority()) 
        ||
          (PriorityScheduler.instance().getMinHardwarePriority() <= ceiling && 
           ceiling <= PriorityScheduler.instance().getMaxHardwarePriority());
           
      ensures true;         // ??
    @*/
  @SCJAllowed(Level.LEVEL_1)
  @SCJRestricted(Phase.INITIALIZE)
	public static void setCeiling(Object target, int ceiling) {
		Monitor monitor = new Monitor(ceiling);
		monitor.attach(target);
	}
}
