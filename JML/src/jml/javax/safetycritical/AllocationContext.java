/**************************************************************************
 * File name  : AllocationContext.java
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

//import javax.safetycritical.annotate.Level;
//import java.lang.SuppressWarnings;
import jml.javax.safetycritical.annotate.SCJAllowed;

//import jml.vm.Memory; 

/**
 * This is the base interface for all memory areas. <br>
 * It is a generalization of the Java Heap to allow for alternate forms of 
 * memory management.<br> 
 * All memory areas implement this interface.
 * 
 * @version 1.0; - May 2012
 * 
 * @author Anders P. Ravn, Aalborg University, 
 * <A HREF="mailto:apr@cs.aau.dk">apr@cs.aau.dk</A>, <br>
 * Hans S&oslash;ndergaard, VIA University College, Denmark, 
 * <A HREF="mailto:hso@viauc.dk">hso@viauc.dk</A>
 * 
 * @scjComment 
 *  - semantic issue: Why is this interface introduced as a public entity? 
 *      No applications declare or access memory areas? <br>
 *  - semantic issue: <code>IllegalThreadStateException</code> 
 *      (cf. SCJ Draft D.1.1 INTERFACE <code>AllocationContext</code>) is not included, 
 *      since only infrastructure can invoke <code>enter</code> methods <br>
 *  - semantic issue: <code>ThrowBoundaryError</code> is not included. 
 *      It must be the responsibility of the exception handlers for
 *      <code>enter</code> methods to make a local copy of the exception 
 *      before propagating it. <br> 
 *   - semantic issue: should <code>newArray</code> and 
 *       <code>newInstance</code> be SCJAllowed. Should they be there at all?
 */

@SCJAllowed
public interface AllocationContext
{  
  /**
   * Gets the amount of allocated memory in this memory area.
   * 
   * @return The amount of memory consumed in bytes.
   */
  /*@ 
    public behavior
      requires true;
      ensures \result >= 0; 
    @*/
  @SCJAllowed
  public long memoryConsumed(); 
  
  /**
   * Gets the amount of memory available for allocation in this memory area.
   * 
   * @return The amount of memory remaining in bytes.
   */
  /*@ 
    public behavior
      requires true;
      ensures \result >= 0; 
    @*/
  @SCJAllowed
  public long memoryRemaining();
  
  /**
   * Gets the size of this memory area.
   * 
   * @return The current size of this memory area.
   */
  /*@ 
    public behavior
      requires true;
      ensures \result >= 0; 
    @*/
  @SCJAllowed
  public long size();
  
}
