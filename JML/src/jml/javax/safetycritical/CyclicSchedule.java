/**************************************************************************
 * File name  : CyclicSchedule.java
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

import jml.javax.safetycritical.annotate.SCJAllowed;

/**
 * The <code>CyclicSchedule</code> class is a container for the frames 
 * to be executed by a cyclic executive.
 * 
 * @version 1.0; - May 2012
 * 
 * @author Anders P. Ravn, Aalborg University, 
 * <A HREF="mailto:apr@cs.aau.dk">apr@cs.aau.dk</A>, <br>
 * Hans S&oslash;ndergaard, VIA University College, Denmark, 
 * <A HREF="mailto:hso@viauc.dk">hso@viauc.dk</A>
 * 
 * @scjComment 
 *
 */
@SCJAllowed
public class CyclicSchedule
{
  private Frame[] frames;

  /*@ public invariant 
        this.getFrames() != null &&
        ( \forall int i; 0 <= i && i < this.getFrames().length; this.getFrames()[i] != null );
    @*/
  
  /**
   * Constructs a <code>CyclicSchedule</code> by copying the frames array 
   * into a private array within the same memory area as this newly 
   * constructed <code>CyclicSchedule</code> object.
   * 
   * @param frames is the frame array.
   */
  /*@ // implementation specification
      requires frames != null &&
        ( \forall int i; 0 <= i && i < frames.length; frames[i] != null );
      
      assignable this.frames;
    
      ensures this.frames == frames; 
      // is it possible to express something about Memory behavior? - see Draft 
    @*/
  @SCJAllowed
  public CyclicSchedule(Frame[] frames) 
  {
    this.frames = frames;
  }

  /**
   * A method used by infrastructure to access the frame array
   * @return Frame array.
   */
  /*@ // implementation specification 
      requires true; 
      assignable \nothing;      
      ensures \result == this.frames;
    @*/
  Frame[] getFrames() 
  {
    return frames;
  }

}
