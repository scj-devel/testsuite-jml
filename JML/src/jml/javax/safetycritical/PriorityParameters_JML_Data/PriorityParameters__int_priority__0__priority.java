/*
 * Test data strategy for jml.javax.safetycritical.PriorityParameters.
 *
 * Generated by JMLUnitNG 1.3 (103), 2013-05-11 05:02 +0200.
 * (do not modify this comment, it is used by JMLUnitNG clean-up routines)
 */

 
package jml.javax.safetycritical.PriorityParameters_JML_Data;

import org.jmlspecs.jmlunitng.iterator.ObjectArrayIterator;
import org.jmlspecs.jmlunitng.iterator.RepeatedAccessIterator;

/**
 * Test data strategy for jml.javax.safetycritical.PriorityParameters. Provides
 * test values for parameter "int priority" 
 * of method "PriorityParameters(int)". 
 * 
 * @author JMLUnitNG 1.3 (103)
 * @version 2013-05-11 05:02 +0200
 */
public class PriorityParameters__int_priority__0__priority
  extends ClassStrategy_int {
  /**
   * @return local-scope values for parameter 
   *  "int priority".
   */
  public RepeatedAccessIterator<?> localValues() {
  	return new ObjectArrayIterator<Object>
  	(new Object[]
  	 { /* add local-scope int values or generators here */ 
  	    1, 50, 100
  	 });
  }
}
