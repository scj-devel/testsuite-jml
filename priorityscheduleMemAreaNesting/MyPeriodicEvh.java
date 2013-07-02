/**************************************************************************
 * File name  : MyPeriodicEvh.java
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

import javax.safetycritical.ManagedMemory;
import javax.safetycritical.MemoryArea;
import javax.safetycritical.MissionSequencer;
import javax.safetycritical.PeriodicEventHandler;
import javax.safetycritical.PeriodicParameters;
import javax.safetycritical.PriorityParameters;
import javax.safetycritical.StorageParameters;

import javax.scj.util.Const;

import unitTest.Assert;

public class MyPeriodicEvh extends PeriodicEventHandler
{
  int n;
  int count = 0;
  static boolean terminating = false;

  MissionSequencer missSeq;

  private class PrivateRun implements Runnable
  {


    @Override
    public void run() {
      Integer obj = new Integer (n);

      MemoryArea[] contexts = MemoryArea.getContexts(obj);
      Assert.assertEquals (Const.PRIVATE_MEM_LEVEL + n + 2, contexts.length-1);
    }
  }

  private PrivateRun privateLogic;


  protected MyPeriodicEvh (PriorityParameters priority,
                           PeriodicParameters periodic,
                           long memSize,  // size of private mem
                           int n,
                           MissionSequencer missSeq)
  {
    super(priority, periodic, new StorageParameters(memSize, null));
    this.n = n;
    this.missSeq = missSeq;
    this.privateLogic = new PrivateRun();
  }

  public void handleAsyncEvent()
  {
    count++;
    Integer obj = new Integer (1);

    if (!terminating)
    {
      MemoryArea[] contexts = MemoryArea.getContexts(obj);
      Assert.assertEquals (Const.PRIVATE_MEM_LEVEL + n, contexts.length-1);

      ManagedMemory.enterPrivateMemory(Const.PRIVATE_MEM_SIZE, privateLogic);
    }

    if (n == 0)
    {
        if (count % 5 == 3)
        {
          terminating = true;
          missSeq.requestSequenceTermination();
        }
    }


  }
}
