/**************************************************************************
 * File name  : HighResolutionTime.java
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
 *   date       init  comment
 *   April 2013 HSO   JML specification added
 *************************************************************************/
package jml.javax.safetycritical;

import jml.javax.safetycritical.annotate.Level;
import jml.javax.safetycritical.annotate.SCJAllowed;

/**
 * <code>HighResolutionTime</code> is the base class for time given by milliseconds plus nanoseconds. <p>
 * A time object in normalized form represents negative time if both components are
 * nonzero and negative, or one is nonzero and negative and the other is zero. <br>
 * For add and subtract operations, negative values behave as they do in Java arithmetic.
 * 
 * @version 1.0; - May 2012
 * 
 * @author Anders P. Ravn, Aalborg University, 
 * <A HREF="mailto:apr@cs.aau.dk">apr@cs.aau.dk</A>, <br>
 * Hans S&oslash;ndergaard, VIA University College, Denmark, 
 * <A HREF="mailto:hso@viauc.dk">hso@viauc.dk</A>
 * 
 * @scjComment
 *  - semantic issue: clock is only meaningful for <code>AbsoluteTime</code> <br>
 *  - semantic issue: Java arithmetic means no overflow detection <br>
 *  - semantic issue: constructor should be protected <br>
 *  - semantic issue: method <code>set</code>: if parameter null, no Exception? <p>
 *  
 *  - implementation issue: 
 *      <code>public int compareTo (Object arg0)</code> is inherited from <code>interface Comparable</code> <br>
 *   - implementation issue: method <code>waitForObject</code> omitted ? <br>
 *   <ul>
 *   <li>
 *    <code>   
 *      public static void waitForObject(java.lang.Object target, HighResolutionTime time)
 *      throws java.lang.InterruptedException 
 *    </code>
 *   </ul>
 */
@SCJAllowed
public abstract class HighResolutionTime implements Comparable<HighResolutionTime>  
{
  Clock clock;
  long millis;
  int nanos;
  
  /*@ 
    public invariant 
    ( getMilliseconds() >= 0L 
     && (0 <= getNanoseconds() && getNanoseconds() < 1000000) ) 
    ||
    ( getMilliseconds() <= 0L 
     && (-1000000 < getNanoseconds() && getNanoseconds() <= 0) );
  @*/
  
  /*@ 
    private behaviour
      requires true;
      assignable \nothing;
      ensures \old(clock) == clock && \old(millis) == millis && \old(nanos) == nanos;
      ensures \result == true;
    @*/ 
  /*@ spec_public @*/ boolean unchanged() {  // problems with tool, if private
    return true;
  }
  
  /*@ 
    private behaviour
      requires true;
      assignable \nothing;
      ensures \old(clock) == clock;
      ensures \result == true;
    @*/ 
  /*@ spec_public @*/ boolean unchangedClock() {
    return true;
  }
  
  /*@
    behaviour
      requires true;
      ensures getMilliseconds() - millis + (getNanoseconds() - nanos ) / 1000000 == 0;
      ensures (getNanoseconds() - nanos ) % 1000000 == 0;
      ensures getClock() == clock;  
    @*/
  /*@ spec_public @*/ HighResolutionTime(long millis, int nanos, Clock clock)   
  {
    setNormalized (millis, nanos);
    this.clock = clock;
  }
  
  /**
   * 
   * @return Returns a reference to the clock associated with this.
   */
  /*@ 
    public behaviour
      requires true;
      ensures unchanged();
//  also 
//    private behaviour
//      assignable \nothing;
//      requires true;     
//      ensures \result == clock;
    @*/
  public final Clock getClock()
  {
    return this.clock;
  }
  
  /**
   * 
   * @return the milliseconds component of the time represented by this.
   */
  /*@
    public behaviour
      requires true;
      ensures unchanged(); 
//    private behaviour
//      assignable \nothing;
//      requires true;     
//      ensures \result == millis; 
   @*/
  public final long getMilliseconds ()
  {
    return this.millis;
  }

  /**
   * 
   * @return the nanoseconds component of the time represented by this.
   */
  /*@ 
    public behaviour
      requires true;
      ensures unchanged(); 
//    private behaviour
//      assignable \nothing;
//      requires true;     
//      ensures \result == nanos;
    @*/
  public final int getNanoseconds ()
  {
    return this.nanos;
  }
  /**
   * Change the value represented by this to that of the given time.
   * 
   * @param time is the new value for this.
   */
  /*@ 
    public behaviour
      requires time != null && this.getClass() == time.getClass();
      ensures getMilliseconds() == time.getMilliseconds(); 
      ensures getNanoseconds() == time.getNanoseconds();
      ensures getClock()  == time.getClock();
    @*/
   public void set(HighResolutionTime time){ 
     if (time != null && this.getClass() == time.getClass() ) 
     {
       this.millis = time.millis;
       this.nanos = time.nanos;
       this.clock  = time.clock;
     }
   }
  
  /**
   * Sets the millisecond component of this to the given argument, and the nanosecond
   * component of this to 0. The clock is unchanged.
   * @param millis is the new value of the millisecond component.
   */
  /*@ 
   public behaviour
     requires true;
     ensures getMilliseconds() == millis; 
     ensures getNanoseconds() == 0;
     ensures unchangedClock();
   @*/
  public void set (long millis)
  {
    this.millis = millis;
    this.nanos  = 0;
  }
  
  /**
   * Sets the millisecond and nanosecond components of this to the given arguments.
   * The millisecond and nanosecond components of this are normalized.
   * The clock is unchanged.
   * @param millis is the new value of the millisecond component.
   * @param nanos is the new value of the nanosecond component.
   */
  /*@ 
    public behaviour
      requires true;
      ensures getMilliseconds() - millis + (getNanoseconds() - nanos ) / 1000000 == 0;
      ensures (getNanoseconds() - nanos ) % 1000000 == 0;
      ensures unchangedClock(); 
//    private behaviour
//       assignable millis, nanos;
   @*/
  public void set (long millis, int nanos)
  {
    setNormalized(millis, nanos);
  }
 
  /**
   * @param time
   * @return is true if the parameter time is of the same type and has the same values as this.
   */
  /*@ 
    public behaviour
      requires true;
   
      ensures ( \result == ( time != null  && 
                             getClass()        == time.getClass() &&
                             getMilliseconds() == time.getMilliseconds()  &&
                             getNanoseconds()  == time.getNanoseconds()   &&
                             getClock()        == time.getClock() )
               );   
      ensures unchanged();  
    @*/
  public boolean equals (HighResolutionTime time)
  {
    if (time == null)
      return false;
    
    return ( this.getClass() == time.getClass() ) &&
           ( this.millis     == time.getMilliseconds() ) &&
           ( this.nanos      == time.getNanoseconds() ) &&
           ( this.clock      == time.getClock() );    
  }
  
  /**
   * @param object
   * @return is true if the parameter time is of the same type and has the same values as this.
   */
  /*@ 
    public behaviour
      requires true;
      ensures ( \result == ( object != null  && 
                             object instanceof HighResolutionTime &&
                             equals ((HighResolutionTime)object) )
               ); 
      ensures unchanged();
    @*/
  public boolean equals (Object object)
  {
    if (object == null)
      return false;
    
    if (object instanceof HighResolutionTime)
      return equals((HighResolutionTime)object);
    
    return false;
  }
 
  /**
   * Compares this with the specified HighResolutionTime time.
   * @param time is the second argument to the comparison.
   * @return the result of the comparison.
   */
  /*@  
    public behaviour
      requires time != null  && 
               this.getClass() == time.getClass() &&
               this.getClock() == time.getClock();   
       
       ensures 
         ( \result < 0 ==> ( (getMilliseconds() < time.getMilliseconds()) 
                            || (getMilliseconds() == time.getMilliseconds() 
                               && getNanoseconds() < time.getNanoseconds()) )  ) 
         ||               
         ( \result > 0 ==> ( (getMilliseconds() == time.getMilliseconds() 
                              && getNanoseconds() > time.getNanoseconds()) 
                            || (getMilliseconds() > time.getMilliseconds()) )  ) 
         ||  
         ( \result ==  0 ==> ( getMilliseconds() == time.getMilliseconds() 
                               && getNanoseconds() == time.getNanoseconds() ) );           
       ensures unchanged();  
    @*/
  public int compareTo (HighResolutionTime time)
  {
    if (time == null)
      throw new NullPointerException("null parameter");
    if (this.getClass() != time.getClass())
      throw new ClassCastException();
    if (this.clock != time.getClock())
      throw new IllegalArgumentException("Different clocks");
    
    if (this.millis < time.getMilliseconds())
      return -1;
    else if (this.millis > time.getMilliseconds())
      return 1;
    else if (this.nanos < time.getNanoseconds())
      return -1;
    else if (this.nanos > time.getNanoseconds())
      return 1;
    else
      return 0;
  }
 
//  public int compareTo (Object arg0)  // ToDo
//  {
//    if (arg0 == null)
//      throw new NullPointerException("null parameter");
//    if (arg0 instanceof HighResolutionTime)
//      return compareTo((HighResolutionTime) arg0);
//    else
//      throw new ClassCastException();
//  }
 
  /*@ 
    public behaviour
      requires true;      
      ensures (* \result is a string representation of this object *);
      ensures unchanged();
    @*/
  public String toString()
  {
    return ("(ms,ns) = (" + millis + ", " + nanos + ")");
  }
  
  /**
   * @scjComment
   *   Omitted ?; - not implemented
   */
  /*@  
    public behaviour
      requires false;  
      ensures  true;      
    @*/
  @SCJAllowed(Level.LEVEL_2)  
  public static void waitForObject(java.lang.Object target,
  HighResolutionTime time) throws java.lang.InterruptedException
  {
    // Not implemented
  }
  
  static final int NANOS_PER_MILLI = 1000000;
  /**
   * Sets the normalized values of millis and nanos in this. 
   */
  final void setNormalized(final long ms, final int ns) 
  {
    /*
     * Examples:
     *   3.12 millis =  3 millis and  120*1000 nanos
     *   0.12 millis =  0 millis and  120*1000 nanos
     *   0.00 millis =  0 millis and    0*1000 nanos
     *  -3.12 millis = -3 millis and -120*1000 nanos 
     *  -0.12 millis =  0 millis and -120*1000 nanos
     *  -0.00 millis = -0 millis and -  0*1000 nanos
     */
    
    // nanos == nanos/NANOS_PER_MILLI + nanos%NANOS_PER_MILLI
	     
    millis = ms + ns/NANOS_PER_MILLI; 
    nanos = ns % NANOS_PER_MILLI;
    if (millis > 0 &&  nanos < 0) { 
      millis--; // millis >= 0
      nanos += NANOS_PER_MILLI;
    } else if (millis < 0 &&  nanos > 0){ 
      millis++; // millis <= 0
      nanos -= NANOS_PER_MILLI; 
    }
  }
  
  
}
