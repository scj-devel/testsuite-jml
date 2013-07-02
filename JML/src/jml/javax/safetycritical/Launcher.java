/**************************************************************************
 * File name  : Launcher.java
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

import jml.javax.safetycritical.CyclicScheduler;
import jml.javax.safetycritical.ImmortalMemory;
import jml.javax.safetycritical.MissionSequencer;
import jml.javax.safetycritical.PriorityScheduler;
import jml.javax.safetycritical.Safelet;
import jml.javax.scj.util.Const;
import unitTest.Assert;

/**
 * This class is used by an application class to launch a Level 0 or 
 * a Level 1 application.
 * 
 * @version 1.0; - May 2012
 * 
 * @author Anders P. Ravn, Aalborg University, 
 * <A HREF="mailto:apr@cs.aau.dk">apr@cs.aau.dk</A>, <br>
 * Hans S&oslash;ndergaard, VIA University College, Denmark, 
 * <A HREF="mailto:hso@viauc.dk">hso@viauc.dk</A>
 * 
 * @scjComment
 *  - The class is not part of the SCJ specification. 
 */
public class Launcher implements Runnable
{
  Safelet app;
  static int level;
  
  public Launcher(Safelet app, int level)
  {
    this.app= app;
    Launcher.level = level;
   
    MemoryArea.allocateBackingStore(Const.BACKING_STORE_SIZE);
    MemoryArea immortalMem = new ImmortalMemory(Const.IMMORTAL_MEM_SIZE);
    immortalMem.executeInArea(this);

    immortalMem.removeArea();
  }
  
  public void run()
  { 
    MissionSequencer seq = app.getSequencer();
    
    MemoryArea[] contexts = MemoryArea.getContexts(seq);
    Assert.assertEquals (Const.IMMORTAL_MEM_LEVEL, contexts.length-1);

    devices.Console.println("Launcher, seq.MemoryAreaLevel: " + contexts[contexts.length-1].getMemoryAreaLevel());
    
    if (level == 0)
    {
      CyclicScheduler.instance().start(seq);
    }
    else
    {
      PriorityScheduler.instance().start();
    }  
  }
}
