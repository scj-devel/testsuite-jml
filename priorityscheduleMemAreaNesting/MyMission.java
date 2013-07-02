/**************************************************************************
 * File name  : MyMission.java
 *
 * This code is available under the license:
 * Creative Commons, http://creativecommons.org/licenses/by-nc-nd/3.0/
 * It is free for non-commercial use.
 *
 * VIA University College, Horsens, Denmark, 2011
 * Hans Soendergaard, hso@viauc.dk
 *
 * Description:
 *
 * Revision history:
 *   date   init  comment
 *
 *************************************************************************/
package test.safetycritical.priorityscheduleMemAreaNesting;

import javax.safetycritical.Clock;
import javax.safetycritical.MemoryArea;
import javax.safetycritical.Mission;
import javax.safetycritical.MissionSequencer;
import javax.safetycritical.PeriodicEventHandler;
import javax.safetycritical.PeriodicParameters;
import javax.safetycritical.PriorityParameters;
import javax.safetycritical.RelativeTime;
import javax.scj.util.Const;
import javax.scj.util.Priorities;

import unitTest.Assert;

public class MyMission extends Mission
{
MissionSequencer missSeq;

  public MyMission (MissionSequencer missSeq)
  {
    this.missSeq = missSeq;
  }

  public void initialize()
  {
    PeriodicEventHandler pevh1 = new MyPeriodicEvh(
        new PriorityParameters(Priorities.PR98),
        new PeriodicParameters(new RelativeTime (Clock.getRealtimeClock()),     // start
                               new RelativeTime (2000, 0, Clock.getRealtimeClock())), // period
        Const.PRIVATE_MEM_SIZE,  // size of private mem
        0, // the number is used for allocation context test
        missSeq);
    pevh1.register();



    PeriodicEventHandler pevh2 = new MyPeriodicEvh(
        new PriorityParameters(Priorities.PR97),
        new PeriodicParameters(new RelativeTime (Clock.getRealtimeClock()),     // start
                               new RelativeTime (3000, 0, Clock.getRealtimeClock())), // period
        Const.PRIVATE_MEM_SIZE,  // size of private mem
        1, // the number is used for allocation context test
        null);
    pevh2.register();

    // For test:

    MemoryArea[] contexts = MemoryArea.getContexts(pevh1);
    Assert.assertEquals (Const.MISSION_MEM_LEVEL, contexts.length-1);

    contexts = MemoryArea.getContexts(pevh2);
    Assert.assertEquals (Const.MISSION_MEM_LEVEL, contexts.length-1);
  }

  public long missionMemorySize ()
  {
    return Const.SCOPED_MEM_SIZE;
  }

}
