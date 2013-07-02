
package jml.vm;

//import icecaptools.IcecapCompileMe;

import jml.javax.safetycritical.AbsoluteTime;
import jml.javax.safetycritical.RelativeTime;
import jml.javax.safetycritical.Clock;
import jml.javax.safetycritical.ClockCallBack;

//import devices.CR16C.KT4585.CR16CRealtimeClock;

public abstract class RealtimeClock extends Clock
{
  private static /*@ spec_public @*/ RealtimeClock instance = new DefaultRealtimeClock();

//  protected RealtimeClock ()
//  {
//    switch (Architecture.architecture)
//    {
//    // case Architecture.CR16_C:            // HSO: commented out: only when JML specifying
//    // instance = new CR16CRealtimeClock(); // The JML tools use Eclipse VM
//    //
//    // break;
//      default:
//        System.out.println("vm.RealtimeClock.RealtimeClock()");
//        instance = new DefaultRealtimeClock();
//    }
//  }

  /*@ 
    public behavior
      requires true;
      ensures \result != null;
    @*/
  public static RealtimeClock instance ()
  {      
    return instance;
  }

  public static class DefaultRealtimeClock extends RealtimeClock
  {
    /* Methods from Clock */
    /*@ 
    public behavior
      requires true;
      ensures \result.getMilliseconds() == System.currentTimeMillis() && 
              \result.getNanoseconds() == 0 &&
              \result.getClock() == this; 
    @*/
    public final AbsoluteTime getTime ()
    {
      AbsoluteTime now = null;
      getTime(now);
      return now;
    }

    /*@ 
    public behavior
      requires true;
      ensures \result.getMilliseconds() == System.currentTimeMillis() && 
              \result.getNanoseconds() == 0 &&
              \result.getClock() == this; 
    @*/
    public AbsoluteTime getTime (AbsoluteTime dest)
    {
      if (dest == null)
        dest = new AbsoluteTime(System.currentTimeMillis(), 0, this);
      else
        dest.set(System.currentTimeMillis(), 0);
      return dest;
    }

    /*@ 
      public behavior
        requires true;
        ensures \result.getMilliseconds() == 1 && 
                \result.getNanoseconds() == 0 &&
                \result.getClock() == this; 
      @*/
    public RelativeTime getResolution ()
    {
      RelativeTime grain = null;
      getResolution(grain);
      return grain;
    }

    /*@ 
      public behavior
        requires true; 
        ensures \result.getMilliseconds() == 1 &&
                \result.getNanoseconds() == 0 && 
                \result.getClock() == this;
      @*/
    public RelativeTime getResolution (RelativeTime dest)
    {
      if (dest == null)
        dest = new RelativeTime(1, 0, this);
      else
        dest.set(1, 0);

      return dest;
    }

    /*@ 
      public behavior
        requires true; 
        ensures \result.getMilliseconds() == 0 &&
                 \result.getNanoseconds() == 0 && 
                 \result.getClock() == this;
     @*/
    public RelativeTime getEpochOffset ()
    {
      return new RelativeTime(0, 0, this);
    }

    /*@ 
      public behavior
        requires true; 
        ensures \result == false;
      @*/
    public boolean drivesEvents ()
    {
      return false;
    }

    public void registerCallBack (AbsoluteTime t, ClockCallBack clockEvent)
    {
    }

    public boolean resetTargetTime (AbsoluteTime time)
    {
      return true;
    }
  }

  /* ==== Clock and Time ================================================ */

  /**
   * Gets the current resulution of the realtime clock. The resolution is
   * the nominal interval between ticks. Returns Relative time in
   * <code>dest</code>.
   * 
   * @return 0 if ok, not zero if an error occur.
   */
  // private static native int getNativeResolution(RelativeTime dest);

  /**
   * Gets the current time of the realtime clock Returns Absolute time in
   * <code>dest</code>.
   * 
   * @return 0 if ok, not zero if an error occor.
   */
  // private static native int getNativeTime(AbsoluteTime dest);

  /**
   * Delay until <code>time</code>.
   * 
   * @param time
   *          is the absolut time
   */
  // public static native void delayNativeUntil(AbsoluteTime time);

  /* ==== Sleeping ====================================================== */

  /**
   * Sleep a relative time.
   * 
   * @param time
   *          The specified time to sleep.
   * @return 0 if requested time has elapsed, -1 if the function fails; see
   *         nanosleep C doc.
   */
  // HSO: June 2013: // HSO: commented out: only when JML specifying; The
  // JML tools use Eclipse VM
  // This function is called in CyclicExecutive.waitForNextFrame
  // public static native void delayNative(RelativeTime time);
}

