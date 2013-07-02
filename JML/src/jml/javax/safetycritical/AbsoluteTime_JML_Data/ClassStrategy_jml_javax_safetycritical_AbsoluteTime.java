/*
 * Test data strategy for jml.javax.safetycritical.AbsoluteTime.
 *
 * Generated by JMLUnitNG 1.3 (103), 2013-05-15 01:01 +0200.
 * (do not modify this comment, it is used by JMLUnitNG clean-up routines)
 */

package jml.javax.safetycritical.AbsoluteTime_JML_Data;


import org.jmlspecs.jmlunitng.iterator.ObjectArrayIterator;
import org.jmlspecs.jmlunitng.iterator.RepeatedAccessIterator;
import jml.javax.safetycritical.PackageStrategy_jml_javax_safetycritical_AbsoluteTime;
import jml.javax.safetycritical.AbsoluteTime;
import jml.javax.safetycritical.Clock;

/**
 * Test data strategy for jml.javax.safetycritical.AbsoluteTime. Provides
 * class-scope test values for type jml.javax.safetycritical.AbsoluteTime.
 * 
 * @author JMLUnitNG 1.3 (103)
 * @version 2013-05-15 01:01 +0200
 */
public class ClassStrategy_jml_javax_safetycritical_AbsoluteTime 
  extends PackageStrategy_jml_javax_safetycritical_AbsoluteTime {
  /**
   * @return class-scope values for type jml.javax.safetycritical.AbsoluteTime.
   */
  public RepeatedAccessIterator<?> classValues() {
    return new ObjectArrayIterator<Object>
    (new Object[] 
  	 { /* add class-scope jml.javax.safetycritical.AbsoluteTime values or generators here */ });
  }

  /**
   * defaultValues() from AbsoluteTime; overridden by HSO
   * @return default values for type AbsoluteTime.
   */
  public RepeatedAccessIterator<?> defaultValues() {
    return new ObjectArrayIterator<Object>
    (new Object[] 
     { /* add default HighResolutionTime values or generators here */ 
        new AbsoluteTime (1L,1,Clock.getRealtimeClock())
     });
  }
  /**
   * The use of reflection can be controlled here for  
   * parameters of type jml.javax.safetycritical.AbsoluteTime
   * in this class by changing the parameters to <code>setReflective</code>
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
  public ClassStrategy_jml_javax_safetycritical_AbsoluteTime() {
    super();
    setReflective(false);
    // uncomment to control the maximum reflective instantiation
    // recursion depth, 0 by default
    // setMaxRecursionDepth(0);
  }
}