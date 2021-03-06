/*
 * Test data strategy for jml.javax.safetycritical.AperiodicEvent.
 *
 * Generated by JMLUnitNG 1.3 (103), 2013-05-12 22:15 +0200.
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
 * Test data strategy for jml.javax.safetycritical.AperiodicEvent. Provides
 * instances of jml.javax.safetycritical.AperiodicEvent for testing, using
 * parameters from constructor tests.
 * 
 * @author JMLUnitNG 1.3 (103)
 * @version 2013-05-12 22:15 +0200
 */
public class AperiodicEvent_InstanceStrategy extends ObjectStrategy {
  /**
   * @return local-scope instances of AperiodicEvent.
   */
  public RepeatedAccessIterator<?> localValues() {
    return new ObjectArrayIterator<Object>
    (new Object[]
     { /* add jml.javax.safetycritical.AperiodicEvent values or generators here */ });
  }

  /**
   * @return default instances of AperiodicEvent, generated
   *  using constructor test parameters.
   */ 
  public RepeatedAccessIterator<jml.javax.safetycritical.AperiodicEvent> defaultValues() {
    final List<RepeatedAccessIterator<jml.javax.safetycritical.AperiodicEvent>> iters = 
      new LinkedList<RepeatedAccessIterator<jml.javax.safetycritical.AperiodicEvent>>();

    // an instantiation iterator for the default constructor
    // (if there isn't one, it will fail silently)
    iters.add(new InstantiationIterator<jml.javax.safetycritical.AperiodicEvent>
      (jml.javax.safetycritical.AperiodicEvent.class, 
       new Class<?>[0], 
       new ObjectArrayIterator<Object[]>(new Object[][]{{}})));

    return new NonNullMultiIterator<jml.javax.safetycritical.AperiodicEvent>(iters);
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
  public AperiodicEvent_InstanceStrategy() {
    super(jml.javax.safetycritical.AperiodicEvent.class);
    setReflective(false);
    // uncomment to control the maximum reflective instantiation
    // recursion depth, 0 by default
    // setMaxRecursionDepth(0);
  }
}
