/*
 * Test data strategy for jml.javax.safetycritical.HighResolutionTime.
 *
 * Generated by JMLUnitNG 1.3 (103), 2013-06-14 10:55 +0200.
 * (do not modify this comment, it is used by JMLUnitNG clean-up routines)
 */

package jml.javax.safetycritical;

import java.util.LinkedList;
import java.util.List;

import org.jmlspecs.jmlunitng.iterator.InstantiationIterator;
import org.jmlspecs.jmlunitng.iterator.IteratorAdapter;
import org.jmlspecs.jmlunitng.iterator.NonNullMultiIterator;
import org.jmlspecs.jmlunitng.iterator.ObjectArrayIterator;
import org.jmlspecs.jmlunitng.iterator.RepeatedAccessIterator;
import org.jmlspecs.jmlunitng.strategy.ObjectStrategy;

/**
 * Test data strategy for jml.javax.safetycritical.HighResolutionTime. Provides
 * instances of jml.javax.safetycritical.HighResolutionTime for testing, using
 * parameters from constructor tests.
 * 
 * @author JMLUnitNG 1.3 (103)
 * @version 2013-06-14 10:55 +0200
 */
public class HighResolutionTime_InstanceStrategy extends ObjectStrategy {
  /**
   * @return local-scope instances of HighResolutionTime.
   */
  public RepeatedAccessIterator<?> localValues() {
    return new ObjectArrayIterator<Object>
    (new Object[]
     { /* add jml.javax.safetycritical.HighResolutionTime values or generators here */ });
  }

  /**
   * @return default instances of HighResolutionTime, generated
   *  using constructor test parameters.
   */ 
  public RepeatedAccessIterator<jml.javax.safetycritical.HighResolutionTime> defaultValues() {
    // abstract classes cannot be constructed
    return new ObjectArrayIterator<jml.javax.safetycritical.HighResolutionTime>(new jml.javax.safetycritical.HighResolutionTime[0]);
  }

  /**
   * Constructor. The boolean parameter to <code>setReflective</code>
   * determines whether or not reflection will be used to generate
   * test objects, and the int parameter to <code>setMaxRecursionDepth</code>
   * determines how many levels reflective generation of self-referential classes
   * will recurse.
   *
   * @see ObjectStrategy#setReflective(boolean)
   * @see ObjectStrategy#setMaxRecursionDepth(int)
   */
  public HighResolutionTime_InstanceStrategy() {
    super(jml.javax.safetycritical.HighResolutionTime.class);
    setReflective(false);
    // uncomment to control the maximum reflective instantiation
    // recursion depth, 0 by default
    // setMaxRecursionDepth(0);
  }
}
