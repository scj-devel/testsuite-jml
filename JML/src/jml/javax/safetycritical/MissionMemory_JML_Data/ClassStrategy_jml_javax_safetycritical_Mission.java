/*
 * Test data strategy for jml.javax.safetycritical.MissionMemory.
 *
 * Generated by JMLUnitNG 1.3 (103), 2013-05-12 01:44 +0200.
 * (do not modify this comment, it is used by JMLUnitNG clean-up routines)
 */

package jml.javax.safetycritical.MissionMemory_JML_Data;


import org.jmlspecs.jmlunitng.iterator.ObjectArrayIterator;
import org.jmlspecs.jmlunitng.iterator.RepeatedAccessIterator;
import jml.javax.safetycritical.PackageStrategy_jml_javax_safetycritical_Mission;
/**
 * Test data strategy for jml.javax.safetycritical.MissionMemory. Provides
 * class-scope test values for type jml.javax.safetycritical.Mission.
 * 
 * @author JMLUnitNG 1.3 (103)
 * @version 2013-05-12 01:44 +0200
 */
public class ClassStrategy_jml_javax_safetycritical_Mission 
  extends PackageStrategy_jml_javax_safetycritical_Mission {
  /**
   * @return class-scope values for type jml.javax.safetycritical.Mission.
   */
  public RepeatedAccessIterator<?> classValues() {
    return new ObjectArrayIterator<Object>
    (new Object[] 
  	 { /* add class-scope jml.javax.safetycritical.Mission values or generators here */ });
  }

  /**
   * The use of reflection can be controlled here for  
   * parameters of type jml.javax.safetycritical.Mission
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
  public ClassStrategy_jml_javax_safetycritical_Mission() {
    super();
    setReflective(false);
    // uncomment to control the maximum reflective instantiation
    // recursion depth, 0 by default
    // setMaxRecursionDepth(0);
  }
}
