/*
 * Test data strategy for jml.javax.safetycritical.MemoryArea.
 *
 * Generated by JMLUnitNG 1.3 (103), 2013-06-16 04:48 +0200.
 * (do not modify this comment, it is used by JMLUnitNG clean-up routines)
 */

 
package jml.javax.safetycritical.MemoryArea_JML_Data;

import org.jmlspecs.jmlunitng.iterator.ObjectArrayIterator;
import org.jmlspecs.jmlunitng.iterator.RepeatedAccessIterator;

/**
 * Test data strategy for jml.javax.safetycritical.MemoryArea. Provides
 * test values for parameter "int number" 
 * of method "java.lang.Object newArray(Class, int)". 
 * 
 * @author JMLUnitNG 1.3 (103)
 * @version 2013-06-16 04:48 +0200
 */
public class newArray__Class_type__int_number__10__number
  extends ClassStrategy_int {
  /**
   * @return local-scope values for parameter 
   *  "int number".
   */
  public RepeatedAccessIterator<?> localValues() {
  	return new ObjectArrayIterator<Object>
  	(new Object[]
  	 { /* add local-scope int values or generators here */ });
  }
}