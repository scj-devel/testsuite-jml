/*
 * Test data strategy for jml.javax.safetycritical.StorageParameters.
 *
 * Generated by JMLUnitNG 1.3 (103), 2013-05-11 06:02 +0200.
 * (do not modify this comment, it is used by JMLUnitNG clean-up routines)
 */

 
package jml.javax.safetycritical.StorageParameters_JML_Data;

import org.jmlspecs.jmlunitng.iterator.ObjectArrayIterator;
import org.jmlspecs.jmlunitng.iterator.RepeatedAccessIterator;

/**
 * Test data strategy for jml.javax.safetycritical.StorageParameters. Provides
 * test values for parameter "long[] sizes" 
 * of method "StorageParameters(long, long[])". 
 * 
 * @author JMLUnitNG 1.3 (103)
 * @version 2013-05-11 06:02 +0200
 */
public class StorageParameters__long_totalBackingStore__long1DArray_sizes__0__sizes
  extends ClassStrategy_long1DArray {
  /**
   * @return local-scope values for parameter 
   *  "long[] sizes".
   */
  public RepeatedAccessIterator<?> localValues() {
  	return new ObjectArrayIterator<Object>
  	(new Object[]
  	 { /* add local-scope long[] values or generators here */ 
  	   new long[] {1L,10L}, new long[] {2L, -2L}
  	 });
  }

  /**
   * Constructor.
   * The maximum length of generated arrays can be controlled here for
   * parameter "long[] sizes" of method "StorageParameters(long, long[])"
   * by changing the parameter to <code>setMaxLength</code>.
   * In addition, the data generators used can be changed by adding 
   * additional data class lines, or by removing some of the automatically 
   * generated ones. Since this is the lowest level of strategy, the 
   * behavior will be exactly as you specify here if you clear the existing 
   * list of classes first.
   *
   * @see NonPrimitiveStrategy#addDataClass(Class<?>)
   * @see NonPrimitiveStrategy#clearDataClasses()
   * @see ArrayStrategy#setMaxLength(int)
   */
  public StorageParameters__long_totalBackingStore__long1DArray_sizes__0__sizes() {
    super();
    // uncomment to control the maximum array length, 1 by default
    // setMaxLength(1); 
    // uncomment to control the maximum reflective instantiation
    // recursion depth, 0 by default
    // setMaxRecursionDepth(0);
  }
}
