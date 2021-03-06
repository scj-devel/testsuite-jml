/*
 * Test data strategy for package jml.javax.safetycritical.
 *
 * Generated by JMLUnitNG 1.3 (103), 2013-05-11 06:02 +0200.
 * (do not modify this comment, it is used by JMLUnitNG clean-up routines)
 */

 package jml.javax.safetycritical;

import org.jmlspecs.jmlunitng.iterator.ObjectArrayIterator;
import org.jmlspecs.jmlunitng.iterator.RepeatedAccessIterator;
import org.jmlspecs.jmlunitng.strategy.ArrayStrategy;

/**
 * Test data strategy for package jml.javax.safetycritical. Provides
 * package-scope test values for type long[].
 * 
 * @author JMLUnitNG 1.3 (103)
 * @version 2013-05-11 06:02 +0200
 */
public class PackageStrategy_long1DArray 
  extends ArrayStrategy {
  /**
   * @return package-scope values for type long[].
   */
  public RepeatedAccessIterator<?> packageValues() {
    return new ObjectArrayIterator<Object>
    (new Object[] 
     { /* add package-scope long[] values or generators here */ });
  }

  /**
   * Constructor. 
   * The maximum length of generated arrays can be controlled here for
   * parameters of type long[]
   * in this package by changing the parameter to <code>setMaxLength</code>.
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
  public PackageStrategy_long1DArray() {
    super(long[].class);
    // uncomment to control the maximum array length, 1 by default
    // setMaxLength(1);
    setReflective(false);
    // uncomment to control the maximum reflective instantiation
    // recursion depth, 0 by default
    // setMaxRecursionDepth(0);
  }
}
