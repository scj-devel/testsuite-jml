/*
 * Test data strategy for jml.javax.safetycritical.MissionMemory.
 *
 * Generated by JMLUnitNG 1.3 (103), 2013-05-12 01:44 +0200.
 * (do not modify this comment, it is used by JMLUnitNG clean-up routines)
 */

 
package jml.javax.safetycritical.MissionMemory_JML_Data;

import org.jmlspecs.jmlunitng.iterator.ObjectArrayIterator;
import org.jmlspecs.jmlunitng.iterator.RepeatedAccessIterator;

/**
 * Test data strategy for jml.javax.safetycritical.MissionMemory. Provides
 * test values for parameter "Mission mission" 
 * of method "void enterToExecute(Mission)". 
 * 
 * @author JMLUnitNG 1.3 (103)
 * @version 2013-05-12 01:44 +0200
 */
public class enterToExecute__Mission_mission__25__mission
  extends ClassStrategy_jml_javax_safetycritical_Mission {
  /**
   * @return local-scope values for parameter 
   *  "Mission mission".
   */
  public RepeatedAccessIterator<?> localValues() {
  	return new ObjectArrayIterator<Object>
  	(new Object[]
  	 { /* add local-scope jml.javax.safetycritical.Mission values or generators here */ });
  }

  /**
   * Constructor.
   * The use of reflection can be controlled here for  
   * "Mission mission" of method "void enterToExecute(Mission)" 
   * by changing the parameters to <code>setReflective</code>
   * and <code>setMaxRecursionDepth<code>.
   * In addition, the data generators used can be changed by adding 
   * additional data class lines, or by removing some of the automatically 
   * generated ones. Since this is the lowest level of strategy, the 
   * behavior will be exactly as you specify here if you clear the existing 
   * list of classes first.
   *
   * @see NonPrimitiveStrategy#addDataClass(Class<?>)
   * @see NonPrimitiveStrategy#clearDataClasses()
   * @see ObjectStrategy#setReflective(boolean)
   * @see ObjectStrategy#setMaxRecursionDepth(int)
   */
  public enterToExecute__Mission_mission__25__mission() {
    super();
    // uncomment to control the maximum reflective instantiation
    // recursion depth, 0 by default
    // setMaxRecursionDepth(0);
  }
}
