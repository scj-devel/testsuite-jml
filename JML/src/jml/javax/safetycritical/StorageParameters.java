/**************************************************************************
 * File name  : StorageParameters.java
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
 * @version 1.0; - May 2012
 * 
 * @author Anders P. Ravn, Aalborg University, 
 * <A HREF="mailto:apr@cs.aau.dk">apr@cs.aau.dk</A>, <br>
 * Hans S&oslash;ndergaard, VIA University College, Denmark, 
 * <A HREF="mailto:hso@viauc.dk">hso@viauc.dk</A>
 * 
 * @scjComment
 *  - The suggested arguments <code>messageLength</code> and <code>stackTraceLength</code>
 *    are vendor specific, thus included in <code>sizes</code>. 
 */
@SCJAllowed
public final class StorageParameters 
{
  long totalBackingStore;
  long[] configurationSizes;
  
  /*@ 
    public invariant (
      (0 <= getBackingStoreSize()) &&             
      (getConfigurationSizes() != null ==> 
         (\forall int i; 0 <= i && i < getConfigurationSizes().length; 
                         getConfigurationSizes()[i] >= 0) ));      
    @*/
  
  /**
   * 
   * @param totalBackingStore size of the backing store reservation for 
   *   worst-case scope usage by the associated <code> ManagedSchedulable</code> object, in bytes
   * 
   * @param sizes is an array of parameters for configuring VM resources 
   *   such as native stack or java stack size. The meanings of the entries
   *   in the array are vendor specific.
   *   The array passed in is not stored in the object. <p>
   */
  /*@ 
    public behavior
      requires ( (totalBackingStore >= 0) &&             
        (sizes != null ==> 
          (\forall int i; 0 <= i && i < sizes.length; sizes[i] >= 0) ));
           
      ensures getBackingStoreSize() == totalBackingStore;  
      ensures getConfigurationSizes() == sizes; 
    @*/
  public StorageParameters(long totalBackingStore, long [] sizes)
  {
    this.totalBackingStore = totalBackingStore;
    this.configurationSizes = sizes;    
  }  
  
  /*@ 
    behavior 
      requires true;       
      ensures unchanged();
    @*/
  long[] getConfigurationSizes()
  {
    return configurationSizes;
  }
  
  /*@ 
    behavior 
      requires true;       
      ensures unchanged();
    @*/
  long getBackingStoreSize()
  {
    return totalBackingStore;
  }
    
  /*@ 
    behaviour
      requires true;
      assignable \nothing;
      ensures \old(totalBackingStore) == totalBackingStore ;
      
      ensures \result == true;
    @*/ 
  /*@ spec_public @*/ boolean unchanged() {  // problems with tool, if private
    return true;
  }
}
