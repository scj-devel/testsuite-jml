/*
 * Test data strategy for package jml.javax.safetycritical.
 *
 * Generated by JMLUnitNG 1.3 (103), 2013-04-07 13:06 +0200.
 * (do not modify this comment, it is used by JMLUnitNG clean-up routines)
 */

 package jml.javax.safetycritical;

import org.jmlspecs.jmlunitng.iterator.ObjectArrayIterator;
import org.jmlspecs.jmlunitng.iterator.RepeatedAccessIterator;
import org.jmlspecs.jmlunitng.strategy.ObjectStrategy;

/**
 * Test data strategy for package jml.javax.safetycritical. Provides
 * package-scope test values for type java.lang.Runnable.
 * 
 * @author JMLUnitNG 1.3 (103)
 * @version 2013-04-07 13:06 +0200
 */
public class PackageStrategy_java_lang_Runnable 
  extends ObjectStrategy {
  /**
   * @return package-scope values for type java.lang.Runnable.
   */
  public RepeatedAccessIterator<?> packageValues() {
    return new ObjectArrayIterator<Object>
    (new Object[] 
     { /* add package-scope java.lang.Runnable values or generators here */ });
  }

  /**
   * Constructor. 
   * The use of reflection can be controlled here for method 
   * parameters of type java.lang.Runnable
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
  public PackageStrategy_java_lang_Runnable() {
    super(java.lang.Runnable.class);
    setReflective(false);
    // uncomment to control the maximum reflective instantiation
    // recursion depth, 0 by default
    // setMaxRecursionDepth(0);
  }
}
