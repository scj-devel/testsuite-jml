/*
 * Test data strategy for jml.javax.safetycritical.AbsoluteTime.
 *
 * Generated by JMLUnitNG 1.3 (103), 2013-05-15 01:01 +0200.
 * (do not modify this comment, it is used by JMLUnitNG clean-up routines)
 */

 
package jml.javax.safetycritical.AbsoluteTime_JML_Data;

import jml.javax.safetycritical.AbsoluteTime;
import jml.javax.safetycritical.Clock;

import org.jmlspecs.jmlunitng.iterator.ObjectArrayIterator;
import org.jmlspecs.jmlunitng.iterator.RepeatedAccessIterator;

/**
 * Test data strategy for jml.javax.safetycritical.AbsoluteTime. Provides
 * test values for parameter "AbsoluteTime dest" 
 * of method "jml.javax.safetycritical.AbsoluteTime add(long, int, AbsoluteTime)". 
 * 
 * @author JMLUnitNG 1.3 (103)
 * @version 2013-05-15 01:01 +0200
 */
public class add__long_millis__int_nanos__AbsoluteTime_dest__25__dest
  extends ClassStrategy_jml_javax_safetycritical_AbsoluteTime {
  /**
   * @return local-scope values for parameter 
   *  "AbsoluteTime dest".
   */
  public RepeatedAccessIterator<?> localValues() {
  	return new ObjectArrayIterator<Object>
  	(new Object[]
  	 { /* add local-scope jml.javax.safetycritical.AbsoluteTime values or generators here */ 
  	    new AbsoluteTime (0L, 0, Clock.getRealtimeClock()) 
  	 });
  }

  /**
   * Constructor.
   * The use of reflection can be controlled here for  
   * "AbsoluteTime dest" of method "jml.javax.safetycritical.AbsoluteTime add(long, int, AbsoluteTime)" 
   * by changing the parameters to <code>setReflective</code>
   * and <code>setMaxRecursionDepth<code>.
   * In addition, the data generators used can be changed by adding 
   * additional data class lines, or by removing some of the automatically 
   * generated ones. Since this is the lowest level of strategy, the 
   * behavior will be exactly as you specify here if you clear the existing 
   * list of classes first.
   *
   * @see NonPrimitiveStrategy#addDataClass(Class<?>)
   * @see NonPrimitiveStrategy#clearDataClasses()
   * @see ObjectStrategy#setReflective(boolean)
   * @see ObjectStrategy#setMaxRecursionDepth(int)
   */
  public add__long_millis__int_nanos__AbsoluteTime_dest__25__dest() {
    super();
    // uncomment to control the maximum reflective instantiation
    // recursion depth, 0 by default
    // setMaxRecursionDepth(0);
  }
}
