/*
 * Test data strategy for jml.javax.safetycritical.AperiodicEvent.
 *
 * Generated by JMLUnitNG 1.3 (103), 2013-05-12 22:15 +0200.
 * (do not modify this comment, it is used by JMLUnitNG clean-up routines)
 */

 
package jml.javax.safetycritical.AperiodicEvent_JML_Data;

import org.jmlspecs.jmlunitng.iterator.ObjectArrayIterator;
import org.jmlspecs.jmlunitng.iterator.RepeatedAccessIterator;

/**
 * Test data strategy for jml.javax.safetycritical.AperiodicEvent. Provides
 * test values for parameter "AperiodicEventHandler handler" 
 * of method "void removeHandler(AperiodicEventHandler)". 
 * 
 * @author JMLUnitNG 1.3 (103)
 * @version 2013-05-12 22:15 +0200
 */
public class removeHandler__AperiodicEventHandler_handler__25__handler
  extends ClassStrategy_jml_javax_safetycritical_AperiodicEventHandler {
  /**
   * @return local-scope values for parameter 
   *  "AperiodicEventHandler handler".
   */
  public RepeatedAccessIterator<?> localValues() {
  	return new ObjectArrayIterator<Object>
  	(new Object[]
  	 { /* add local-scope jml.javax.safetycritical.AperiodicEventHandler values or generators here */ });
  }

  /**
   * Constructor.
   * The use of reflection can be controlled here for  
   * "AperiodicEventHandler handler" of method "void removeHandler(AperiodicEventHandler)" 
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
  public removeHandler__AperiodicEventHandler_handler__25__handler() {
    super();
    // uncomment to control the maximum reflective instantiation
    // recursion depth, 0 by default
    // setMaxRecursionDepth(0);
  }
}
