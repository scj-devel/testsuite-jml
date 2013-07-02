/**************************************************************************
 * File name  : PeriodicEventHandler.java
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

import jml.javax.safetycritical.annotate.Level;
import jml.javax.safetycritical.annotate.SCJAllowed;

import jml.javax.scj.util.Priorities;
/**
 * This class permits the automatic periodic execution of code.
 * 
 * @version 1.0; - May 2012
 * 
 * @author Anders P. Ravn, Aalborg University, 
 * <A HREF="mailto:apr@cs.aau.dk">apr@cs.aau.dk</A>, <br>
 * Hans S&oslash;ndergaard, VIA University College, Denmark, 
 * <A HREF="mailto:hso@viauc.dk">hso@viauc.dk</A>
 * 
 * @scjComment
 *  - SCJ issue: One constructor only.
 */

@SCJAllowed
public abstract class PeriodicEventHandler extends ManagedEventHandler
{  
  /*@ requires (priority != null) &&
                (Priorities.MIN_PRIORITY <= priority.getPriority() &&
                   priority.getPriority() <= Priorities.MAX_PRIORITY); 
                // the above is the invariant of Priorities; necessary to put it here?
      requires release  != null;
      requires storage  != null;         
      
      assignable this.priority, this.release;
      
      ensures true;
      
    @*/
  public PeriodicEventHandler(PriorityParameters priority, 
      PeriodicParameters release, StorageParameters storage)
  {  
    super (priority, release, storage);
  }
  
  /*@ requires true; 
      assignable \nothing;
      ensures true;  // ??
    @*/
  public final void register()
  {
    super.register();
  }
  
  /*@ requires true; 
      assignable \nothing;
      ensures true;  // ??
    @*/
  @SCJAllowed(Level.LEVEL_1)
  public HighResolutionTime getActualStartTime()
  {
    // ToDo: implementation
    return null;
  }
  
  /*@ requires true; 
      assignable \nothing;
      ensures true;  // ??
    @*/
  @SCJAllowed(Level.LEVEL_1)
  public HighResolutionTime getEffectiveStartTime()
  {
    // ToDo: implementation
    return null;
  }
  
  /*@ requires true; 
      assignable \nothing;
      ensures true;  // ??
    @*/
  @SCJAllowed(Level.LEVEL_1)
  public AbsoluteTime getNextReleaseTime()
  {
    // ToDo: implementation
    return null;
  }
  
  /*@ requires true; 
      assignable \nothing;
      ensures true;  // ??
    @*/
  @SCJAllowed(Level.LEVEL_1)
  public AbsoluteTime getNextReleaseTime(AbsoluteTime dest)
  {
    // ToDo: implementation
    return null;
  }
  
  /*@ requires true; 
      assignable \nothing;
      ensures true;  // ??
    @*/
  @SCJAllowed(Level.LEVEL_1)
  public HighResolutionTime getRequestedStartTime()
  {
    // ToDo: implementation
    return null;
  }
}
