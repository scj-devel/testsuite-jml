package jml.javax.safetycritical;

import jml.javax.safetycritical.annotate.SCJAllowed;


/**
* The frames array represents the order in which event handlers are to be scheduled. <br>
* Each <code>Frame</code> contains a duration of the frame and a list of periodic handlers to be 
* executed during that time. <br>
* Note that a <code>Frame</code> may have zero periodic handlers associated with them. 
* This represents a period of time during which the <code>CyclicExecutive</code> is idle.
* 
* @version 1.0; - May 2012
* 
* @author Anders P. Ravn, Aalborg University, 
* <A HREF="mailto:apr@cs.aau.dk">apr@cs.aau.dk</A>, <br>
* Hans S&oslash;ndergaard, VIA University College, Denmark, 
* <A HREF="mailto:hso@viauc.dk">hso@viauc.dk</A>
* 
* @scjComment 
*  - semantic issue: Negative duration. It is checked in the constructor. <br>
*  - semantic issue: Null duration. It is checked in the constructor.
*/
@SCJAllowed
public final class Frame 
{
   private RelativeTime duration;
   private PeriodicEventHandler[] handlers;
  
   /*@ public invariant 
         this.getDuration() != null && this.getHandlers() != null &&
         ( (this.getDuration().getMilliseconds() > 0 && this.getDuration().getNanoseconds() >= 0) ||
           (this.getDuration().getMilliseconds() == 0 && this.getDuration().getNanoseconds() > 0) );
     @*/

   /**
    * Constructor for a frame.
    * 
    * @param duration is a <code>RelativeTime</code> object.
    * @param handlers is the list of periodic handlers.
    */
   /*@ // implementation specification
       requires duration != null && handlers != null;
       requires (duration.getMilliseconds() > 0 && duration.getNanoseconds() >= 0) ||
                (duration.getMilliseconds() == 0 && duration.getNanoseconds() > 0);
       
       assignable this.duration, this.handlers;
    
       ensures this.duration == duration && this.handlers == handlers; 
       // is it possible to express something abour Memory behavior? - see Draft 
     @*/
   @SCJAllowed
   public Frame(RelativeTime duration, PeriodicEventHandler[] handlers) 
   {
     if (duration == null)
       throw new IllegalArgumentException("duration is null");
     if (duration.getMilliseconds() < 0 || duration.getNanoseconds() < 0)
       throw new IllegalArgumentException("negative duration");
     
     this.duration = duration;
     this.handlers = handlers;
   }
  
   /**
    * 
    * @return The list of handlers
    */
   /*@ // implementation specification 
       requires true; 
       assignable \nothing;      
       ensures \result == this.handlers;
     @*/
   PeriodicEventHandler[] getHandlers() 
   {
     return handlers;
   }
  
   /**
    * 
    * @return The duration
    */
   /*@ // implementation specification 
       requires true; 
       assignable \nothing;      
       ensures \result == this.duration;
     @*/
   RelativeTime getDuration() 
   {
     return duration;
   }
}
