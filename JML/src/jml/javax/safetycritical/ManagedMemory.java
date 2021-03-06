/**************************************************************************
 * File name  : ManagedMemory.java
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

/**
 * Managed memory is a scoped memory area that is managed by a mission.
 * 
 * @version 1.0; - May 2012
 * 
 * @author Anders P. Ravn, Aalborg University, 
 * <A HREF="mailto:apr@cs.aau.dk">apr@cs.aau.dk</A>, <br>
 * Hans S&oslash;ndergaard, VIA University College, Denmark, 
 * <A HREF="mailto:hso@viauc.dk">hso@viauc.dk</A>
 * 
 * @scjComment 
 *  SCJ issue: The  sub-classes <code>MissionMemory</code> and 
 *    <code>PrivateMemory</code> should not be accessible to applications. 
 *    At most to the infrastructure or even better left out of the specification.
 *  <p>
 *  SCJ issue: Omitting the following method ? 
 *    <ul><code> 
 *      <li>public static ManagedMemory getCurrentManagedMemory() 
 *    </code></ul>
 *  <p>
 *  Applications have nothing to do with Memories, do they? 
 *  <p>
 *  SCJ issue: Placing the portal object here means that a portal is 
 *    available in private memories - for sharing between schedulable objects! 
 *
 */
@SCJAllowed
public abstract class ManagedMemory extends MemoryArea implements
    ScopedAllocationContext
{
  Object portal;
  
  /*@ 
    behavior
      requires size >= 0;    
      ensures size() == size && memoryConsumed() == 0;  
    @*/
  ManagedMemory(int size) 
  {    
    super(size);
  }
  
  /**
   *  @scjComment
   *   Omitting the method ? <br>
   *   Hard to check proper use.
   * @return The current managed memory.
   * 
   * @throws IllegalStateException When called from immortal.
   */
//  @SCJAllowed 
//  public static ManagedMemory getCurrentManagedMemory()  // not in Draft any more
//  {
//    return (ManagedMemory)MemoryArea.getCurrentMemory();
//  }
  
  /**
   * Resizes current managed memory.
   * @param size is the new size in bytes.
   */
//  @SCJAllowed(Level.INFRASTRUCTURE)  // not in Draft any more
//  final void resize(long size)
//  {
//    
//  }

  /** This method causes the calling schedulable object to enter a nested private memory
   * area. <p>
   * If the private memory does not exist, create one; otherwise set its size; then, 
   * enter ; and finally, set the size of private memory to zero.  
   * <p>
   * The private memory object representing the inner scope memory area is reused
   * on subsequent calls to <code>enterPrivateMemory</code> during the lifetime of the current
   * memory area. 
   *  
   */
  /*@ 
    public behavior 
      requires size >= 0 && logic != null;
      ensures true;
    @*/
  @SCJAllowed  
  public static void enterPrivateMemory(int size, Runnable logic) 
  {
	  MemoryArea.currentActiveArea.enterMemory(size, logic);
  }
  
  /*@ 
    public behavior
      requires obj != null && logic != null;
      ensures true;
    @*/
  @SCJAllowed  
  public static void executeInAreaOf(Object obj, Runnable logic) 
  {
    MemoryArea mem = MemoryArea.getMemoryArea(obj);
    mem.executeInArea(logic);
  }
  
  /*@ 
    public behavior
      requires logic != null;
      ensures true;
    @*/
  @SCJAllowed  
  public static void executeInOuterArea(Runnable logic) 
  {
    // not implemented
  }
  
  /**
   * 
   * @return the size of the remaining memory available to the current 
   *   ManagedMemory area.
   */
  /*@ 
    public behavior
      requires true;
      ensures \result == size() - memoryConsumed();
    @*/
  @SCJAllowed  
  public long getRemainingBackingStore()
  {
    return (long)(delegate.getSize() - delegate.consumedMemory());
  }

  @SCJAllowed(Level.INFRASTRUCTURE)
  Object getPortal()
  {
    return portal;
  }

  @SCJAllowed(Level.INFRASTRUCTURE)
  void setPortal (Object value)
  {
    this.portal = value;
  }
}
