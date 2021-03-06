/*
 * Test data strategy for jml.javax.safetycritical.PriorityScheduler.
 *
 * Generated by JMLUnitNG 1.3 (103), 2013-05-12 19:04 +0200.
 * (do not modify this comment, it is used by JMLUnitNG clean-up routines)
 */

package jml.javax.safetycritical.PriorityScheduler_JML_Data;


import org.jmlspecs.jmlunitng.iterator.ObjectArrayIterator;
import org.jmlspecs.jmlunitng.iterator.RepeatedAccessIterator;
import jml.javax.safetycritical.PackageStrategy_int1DArray;
/**
 * Test data strategy for jml.javax.safetycritical.PriorityScheduler. Provides
 * class-scope test values for type int[].
 * 
 * @author JMLUnitNG 1.3 (103)
 * @version 2013-05-12 19:04 +0200
 */
public class ClassStrategy_int1DArray 
  extends PackageStrategy_int1DArray {
  /**
   * @return class-scope values for type int[].
   */
  public RepeatedAccessIterator<?> classValues() {
    return new ObjectArrayIterator<Object>
    (new Object[] 
  	 { /* add class-scope int[] values or generators here */ });
  }

  /**
   * The maximum length of generated arrays can be controlled here for
   * parameters of type int[]
   * in this class by changing the parameter to <code>setMaxLength</code>.
   * In addition, the data generators used can be changed by adding 
   * additional data class lines, or by removing some of the automatically 
   * generated ones. Note that lower-level strategies can override any 
   * behavior specified here by calling the same control methods in 
   * their own constructors.
   *
   * @see NonPrimitiveStrategy#addDataClass(Class<?>)
   * @see NonPrimitiveStrategy#clearDataClasses()
   * @see ArrayStrategy#setMaxLength(int)
   */
  public ClassStrategy_int1DArray() {
    super();
    // uncomment to control the maximum array length, 1 by default
    // setMaxLength(1); 
    setReflective(false);
    // uncomment to control the maximum reflective instantiation
    // recursion depth, 0 by default
    // setMaxRecursionDepth(0);
  }
}
