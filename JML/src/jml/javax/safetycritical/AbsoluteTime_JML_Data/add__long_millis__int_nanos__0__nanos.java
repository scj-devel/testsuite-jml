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
 * test values for parameter "int nanos" 
 * of method "jml.javax.safetycritical.AbsoluteTime add(long, int)". 
 * 
 * @author JMLUnitNG 1.3 (103)
 * @version 2013-05-15 01:01 +0200
 */
public class add__long_millis__int_nanos__0__nanos
  extends ClassStrategy_int {
  /**
   * @return local-scope values for parameter 
   *  "int nanos".
   */
  public RepeatedAccessIterator<?> localValues() {
  	return new ObjectArrayIterator<Object>
  	(new Object[]
  	 { /* add local-scope int values or generators here */ });
  }
}
