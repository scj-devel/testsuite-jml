/*
 * Test data strategy for jml.javax.safetycritical.ManagedMemory.
 *
 * Generated by JMLUnitNG 1.3 (103), 2013-05-12 02:28 +0200.
 * (do not modify this comment, it is used by JMLUnitNG clean-up routines)
 */

 
package jml.javax.safetycritical.ManagedMemory_JML_Data;

import org.jmlspecs.jmlunitng.iterator.ObjectArrayIterator;
import org.jmlspecs.jmlunitng.iterator.RepeatedAccessIterator;

/**
 * Test data strategy for jml.javax.safetycritical.ManagedMemory. Provides
 * test values for parameter "int size" 
 * of method "void enterPrivateMemory(int, Runnable)". 
 * 
 * @author JMLUnitNG 1.3 (103)
 * @version 2013-05-12 02:28 +0200
 */
public class enterPrivateMemory__int_size__Runnable_logic__10__size
  extends ClassStrategy_int {
  /**
   * @return local-scope values for parameter 
   *  "int size".
   */
  public RepeatedAccessIterator<?> localValues() {
  	return new ObjectArrayIterator<Object>
  	(new Object[]
  	 { /* add local-scope int values or generators here */ });
  }
}
