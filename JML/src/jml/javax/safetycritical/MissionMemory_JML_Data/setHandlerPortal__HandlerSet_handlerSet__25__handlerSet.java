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
 * test values for parameter "HandlerSet handlerSet" 
 * of method "void setHandlerPortal(HandlerSet)". 
 * 
 * @author JMLUnitNG 1.3 (103)
 * @version 2013-05-12 01:44 +0200
 */
public class setHandlerPortal__HandlerSet_handlerSet__25__handlerSet
  extends ClassStrategy_jml_javax_safetycritical_HandlerSet {
  /**
   * @return local-scope values for parameter 
   *  "HandlerSet handlerSet".
   */
  public RepeatedAccessIterator<?> localValues() {
  	return new ObjectArrayIterator<Object>
  	(new Object[]
  	 { /* add local-scope jml.javax.safetycritical.HandlerSet values or generators here */ });
  }

  /**
   * Constructor.
   * The use of reflection can be controlled here for  
   * "HandlerSet handlerSet" of method "void setHandlerPortal(HandlerSet)" 
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
  public setHandlerPortal__HandlerSet_handlerSet__25__handlerSet() {
    super();
    // uncomment to control the maximum reflective instantiation
    // recursion depth, 0 by default
    // setMaxRecursionDepth(0);
  }
}
