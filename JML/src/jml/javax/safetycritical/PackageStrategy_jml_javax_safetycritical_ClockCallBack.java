/*
 * Test data strategy for package jml.javax.safetycritical.
 *
 * Generated by JMLUnitNG 1.3 (103), 2013-04-07 16:16 +0200.
 * (do not modify this comment, it is used by JMLUnitNG clean-up routines)
 */

 package jml.javax.safetycritical;

import org.jmlspecs.jmlunitng.iterator.ObjectArrayIterator;
import org.jmlspecs.jmlunitng.iterator.RepeatedAccessIterator;
import org.jmlspecs.jmlunitng.strategy.ObjectStrategy;

/**
 * Test data strategy for package jml.javax.safetycritical. Provides
 * package-scope test values for type jml.javax.safetycritical.ClockCallBack.
 * 
 * @author JMLUnitNG 1.3 (103)
 * @version 2013-04-07 16:16 +0200
 */
public class PackageStrategy_jml_javax_safetycritical_ClockCallBack 
  extends ObjectStrategy {
  /**
   * @return package-scope values for type jml.javax.safetycritical.ClockCallBack.
   */
  public RepeatedAccessIterator<?> packageValues() {
    return new ObjectArrayIterator<Object>
    (new Object[] 
     { /* add package-scope jml.javax.safetycritical.ClockCallBack values or generators here */ });
  }

  /**
   * Constructor. 
   * The use of reflection can be controlled here for method 
   * parameters of type jml.javax.safetycritical.ClockCallBack
   * in this package by changing the parameters to <code>setReflective</code>
   * and <code>setMaxRecursionDepth<code>.
   * In addition, the data generators used can be changed by adding 
   * additional data class lines, or by removing some of the automatically 
   * generated ones. Note that lower-level strategies can override any 
   * behavior specified here by calling the same control methods in 
   * their own constructors.
   *
   * @see NonPrimitiveStrategy#addDataClass(Class<?>)
   * @see NonPrimitiveStrategy#clearDataClasses()
   * @see ObjectStrategy#setReflective(boolean)
   * @see ObjectStrategy#setMaxRecursionDepth(int)
   */
  public PackageStrategy_jml_javax_safetycritical_ClockCallBack() {
    super(jml.javax.safetycritical.ClockCallBack.class);
    setReflective(false);
    // uncomment to control the maximum reflective instantiation
    // recursion depth, 0 by default
    // setMaxRecursionDepth(0);
  }
}
