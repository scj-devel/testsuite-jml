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
 * test values for parameter "Class type" 
 * of method "java.lang.Object newInstance(Class)". 
 * 
 * @author JMLUnitNG 1.3 (103)
 * @version 2013-06-16 04:48 +0200
 */
public class newInstance__Class_type__10__type
  extends ClassStrategy_java_lang_Class {
  /**
   * @return local-scope values for parameter 
   *  "Class type".
   */
  public RepeatedAccessIterator<?> localValues() {
  	return new ObjectArrayIterator<Object>
  	(new Object[]
  	 { /* add local-scope java.lang.Class values or generators here */ });
  }

  /**
   * Constructor.
   * The use of reflection can be controlled here for  
   * "Class type" of method "java.lang.Object newInstance(Class)" 
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
  public newInstance__Class_type__10__type() {
    super();
    // uncomment to control the maximum reflective instantiation
    // recursion depth, 0 by default
    // setMaxRecursionDepth(0);
  }
}
