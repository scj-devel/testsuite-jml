/*
 * Test data strategy for jml.javax.safetycritical.AbsoluteTime.
 *
 * Generated by JMLUnitNG 1.3 (103), 2013-05-15 01:01 +0200.
 * (do not modify this comment, it is used by JMLUnitNG clean-up routines)
 */

 
package jml.javax.safetycritical.AbsoluteTime_JML_Data;

import org.jmlspecs.jmlunitng.iterator.ObjectArrayIterator;
import org.jmlspecs.jmlunitng.iterator.RepeatedAccessIterator;

/**
 * Test data strategy for jml.javax.safetycritical.AbsoluteTime. Provides
 * test values for parameter "long millis" 
 * of method "AbsoluteTime(long, int, Clock)". 
 * 
 * @author JMLUnitNG 1.3 (103)
 * @version 2013-05-15 01:01 +0200
 */
public class AbsoluteTime__long_millis__int_nanos__Clock_clock__25__millis
  extends ClassStrategy_long {
  /**
   * @return local-scope values for parameter 
   *  "long millis".
   */
  public RepeatedAccessIterator<?> localValues() {
  	return new ObjectArrayIterator<Object>
  	(new Object[]
  	 { /* add local-scope long values or generators here */ 
  	    2L
  	 });
  }
}
