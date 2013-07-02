/**************************************************************************
 * File name  : RelativeTime.java
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

import jml.javax.safetycritical.Clock;
import jml.javax.safetycritical.annotate.SCJAllowed;

/**
 * An object that represents a duration in milliseconds and nanoseconds
 * 
 * @version 1.0; - May 2012
 * 
 * @author Anders P. Ravn, Aalborg University, 
 * <A HREF="mailto:apr@cs.aau.dk">apr@cs.aau.dk</A>, <br>
 * Hans S&oslash;ndergaard, VIA University College, Denmark, 
 * <A HREF="mailto:hso@viauc.dk">hso@viauc.dk</A>
 * 
 * @scjComment
 *  - semantic issue: <code>Clock</code> is meaningless and ignored (RTSJ thinks otherwise).
 *   
 */
@SCJAllowed
public class RelativeTime extends HighResolutionTime 
{
  /**
   * Equivalent to <code>RelativeTime(0,0)</code>.
   */
  /*@ 
    public behaviour
      requires true;
      ensures getMilliseconds() == 0L && getNanoseconds() == 0;
    @*/
  public RelativeTime()
  {
    this (0, 0);
  }

  /**
   * Constructs a <code>RelativeTime</code> object representing a duration based on the parameters.
   * @param millis is the milliseconds.
   * @param nanos is the nanoseconds.
   */
  /*@ 
    public behaviour
      requires true;
      ensures getMilliseconds() - millis + (getNanoseconds() - nanos ) / 1000000 == 0;
      ensures (getNanoseconds() - nanos ) % 1000000 == 0;   
   @*/
  public RelativeTime(long millis, int nanos)
  {
    this (millis, nanos, null); 
  } 
  
  /**
   * Equivalent to <code>new RelativeTime(0, 0, clock)</code>.
   * @param clock is the clock argument.
   */
  /*@ 
    public behaviour
      requires clock != null;
      ensures getMilliseconds() == 0L && getNanoseconds() == 0;
      ensures getClock() == clock;
    @*/
  public RelativeTime (Clock clock)
  {
    super (0, 0, clock);
  }
  
  /**
   * Constructs a <code>RelativeTime</code> object representing a duration based on the parameters.
   * @param millis is the milliseconds
   * @param nanos is the nanoseconds
   * @param clock is the clock
   */
  /*@ 
    public behaviour
      requires true;
      ensures getMilliseconds() - millis + (getNanoseconds() - nanos ) / 1000000 == 0;
      ensures (getNanoseconds() - nanos ) % 1000000 == 0; 
      ensures getClock() == clock;    
    @*/
  public RelativeTime(long millis, int nanos, Clock clock)
  {
    super (millis, nanos, clock);
  }
  
  /**
   * Makes a new <code>RelativeTime</code> object from the given <code>RelativeTime</code> object.
   * 
   * @param time is the copied object.  
   */
  /*@
    public behaviour
      requires time != null;
      ensures equals(time);
      ensures time.unchanged();
    @*/
  public RelativeTime(RelativeTime time)
  { 
    this (time.getMilliseconds(), time.getNanoseconds(), time.getClock());
  }
  
  /**
   * Creates a new object representing the result of adding millis and nanos to the values
   * from this
   * @param millis is the milliseconds to be added.
   * @param nanos is the nanoseconds to be added.
   * @return the new object with the added durations.
   */
  /*@ 
    public behaviour
      requires true;
      ensures \result != null && \result instanceof RelativeTime;
      ensures \result.getMilliseconds() - getMilliseconds() - millis + 
                (\result.getNanoseconds() - getNanoseconds() - nanos) / 1000000 == 0;      
      ensures (\result.getNanoseconds() - getNanoseconds() - nanos ) % 1000000 == 0; 
      ensures unchanged();     
    @*/
  public RelativeTime add (long millis, int nanos)
  {
    return new RelativeTime(this.millis + millis, this.nanos + nanos);
  }

  /**
   * Creates a new object representing the result of adding <code>time</code> to the value of this
   * @param time is the duration to be added.
   * @return the new object with the added durations.
   */
  /*@ 
    public behaviour
      requires time != null;
      
      ensures \result != null && \result instanceof RelativeTime;
      
      ensures \result.getMilliseconds() - getMilliseconds() - time.getMilliseconds() + 
                (\result.getNanoseconds() - getNanoseconds() - time.getNanoseconds()) / 1000000 == 0;      
      ensures (\result.getNanoseconds() - getNanoseconds() - time.getNanoseconds()) % 1000000 == 0;       
      ensures time.unchanged();
      ensures unchanged();
   @*/
  public RelativeTime add (RelativeTime time)
  {
	  if (time == null)
	    throw new IllegalArgumentException("time is null");
	
    return new RelativeTime(this.millis + time.getMilliseconds(),
                            this.nanos + time.getNanoseconds());
  }

  /**
   * Returns an object containing the value resulting from adding millis and nanos to this.
   * The result is stored in <code>dest</code>.
   * @param millis millis is the milliseconds to be added.
   * @param nanos is the nanoseconds to be added.
   * @param dest is the destination, if initially null a <code>new RelativeTime()</code> object is created.
   * @return the <code>dest</code> object with the resulting value.
   */
  /*@ 
    public behaviour
      requires true;
      
      ensures \result != null && \result instanceof RelativeTime;
      
      ensures \result.getMilliseconds() - getMilliseconds() - millis + 
                (\result.getNanoseconds() - getNanoseconds() - nanos) / 1000000 == 0;      
      ensures (\result.getNanoseconds() - getNanoseconds() - nanos)  % 1000000 == 0;
      
      ensures \result == dest;
      ensures unchanged();
    @*/
  public RelativeTime add (long millis, int nanos, RelativeTime dest)
  {
    if (dest == null) {
      dest = new RelativeTime(this.millis + millis, this.nanos  + nanos);
    } else {
      dest.set(this.millis + millis, this.nanos  + nanos);
    }
    return dest;
  }

  /**
   * Returns an object containing the value resulting from adding <code>time</code> to this.
   * The result is stored in <code>dest</code>.
   * @param time is the time to be added
   * @param dest is the destination, if null a <code>new RelativeTime()</code> object is created
   * @return the <code>dest</code> object with the resulting value.
   */
  /*@    
    public behaviour
      requires time != null;
   
      ensures \result != null && \result instanceof RelativeTime;
      
      ensures \result.getMilliseconds() - getMilliseconds() - time.getMilliseconds() + 
                (\result.getNanoseconds() - getNanoseconds() - time.getNanoseconds()) / 1000000 == 0;      
      ensures (\result.getNanoseconds() - getNanoseconds() - time.getNanoseconds()) % 1000000 == 0;       
      ensures time.unchanged();
      ensures unchanged();
    @*/
  public RelativeTime add (RelativeTime time, RelativeTime dest)
  {
    if (time == null)
      throw new IllegalArgumentException("time is null");
    
    return this.add(time.getMilliseconds(), time.getNanoseconds(), dest);
  }

  /**
   * Creates a new <code>RelativeTime</code> object representing the result 
   * of subtracting <code>time</code> from the value of this.
   * @param time the value to be subtracted.
   * @return the difference between durations.
   */
  /*@ 
    public behaviour
      requires time != null;
      requires time.clock == this.clock; 
      
      ensures \result != null && \result instanceof RelativeTime;
      
      ensures \result.getMilliseconds() - getMilliseconds() + time.getMilliseconds() + 
                (\result.getNanoseconds() - getNanoseconds() + time.getNanoseconds()) / 1000000 == 0;      
      ensures (\result.getNanoseconds() - getNanoseconds() + time.getNanoseconds()) % 1000000 == 0;
      ensures \result.getClock() == this.getClock();
      ensures time.unchanged();
      ensures unchanged();
    @*/
  public RelativeTime subtract (RelativeTime time)
  {
    if (time == null)
      throw new IllegalArgumentException("time is null");
    
//    long ms = this.millis - time.getMilliseconds();
//    int ns  = this.nanos  - time.getNanoseconds();
    
    // normalize: 
//    long millis = ms + ns/NANOS_PER_MILLI; 
//    int nanos = ns % NANOS_PER_MILLI;
//    if (millis > 0 &&  nanos < 0) { 
//      millis--; // millis >= 0
//      nanos += NANOS_PER_MILLI;
//    } else if (millis < 0 &&  nanos > 0){ 
//      millis++; // millis <= 0
//      nanos -= NANOS_PER_MILLI; 
//    }
    
//    return new RelativeTime(millis, nanos, time.getClock());
    
    return new RelativeTime(this.millis - time.getMilliseconds(), 
                            this.nanos  - time.getNanoseconds(), 
                            time.getClock());
  }

  /**
   * Creates a new <code>RelativeTime</code> object representing the result 
   * of subtracting <code>time</code> from the value of this
   * The result is stored in <code>dest</code>.
   * @param time is the duration to be subtracted
   * @param dest is the destination, if  null a <code>new RelativeTime()</code> object is created
   * @return the <code>dest</code> object with the resulting value.
   */
  /*@ 
    public behaviour
      requires time != null;
   
      ensures \result != null && \result instanceof RelativeTime;
   
      ensures \result.getMilliseconds() - getMilliseconds() + time.getMilliseconds() + 
               (\result.getNanoseconds() - getNanoseconds() + time.getNanoseconds()) / 1000000 == 0;      
      ensures (\result.getNanoseconds() - getNanoseconds() + time.getNanoseconds()) % 1000000 == 0;
      
      ensures \result == dest;
      ensures time.unchanged();
      ensures unchanged();
   @*/
  public RelativeTime subtract (RelativeTime time, RelativeTime dest)
  {
    if (time == null)
      throw new IllegalArgumentException("time is null");
    
    if (dest == null) {
      dest = new RelativeTime(this.millis - time.millis, this.nanos  - time.nanos);
    } else {
      dest.set(this.millis - time.millis, this.nanos  - time.nanos);
    }
    return dest;
  }
}
