/*
 * Test data strategy for jml.javax.safetycritical.Services.
 *
 * Generated by JMLUnitNG 1.3 (103), 2013-05-13 00:16 +0200.
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
 * Test data strategy for jml.javax.safetycritical.Services. Provides
 * instances of jml.javax.safetycritical.Services for testing, using
 * parameters from constructor tests.
 * 
 * @author JMLUnitNG 1.3 (103)
 * @version 2013-05-13 00:16 +0200
 */
public class Services_InstanceStrategy extends ObjectStrategy {
  /**
   * @return local-scope instances of Services.
   */
  public RepeatedAccessIterator<?> localValues() {
    return new ObjectArrayIterator<Object>
    (new Object[]
     { /* add jml.javax.safetycritical.Services values or generators here */ });
  }

  /**
   * @return default instances of Services, generated
   *  using constructor test parameters.
   */ 
  public RepeatedAccessIterator<jml.javax.safetycritical.Services> defaultValues() {
    final List<RepeatedAccessIterator<jml.javax.safetycritical.Services>> iters = 
      new LinkedList<RepeatedAccessIterator<jml.javax.safetycritical.Services>>();

    // an instantiation iterator for the default constructor
    // (if there isn't one, it will fail silently)
    iters.add(new InstantiationIterator<jml.javax.safetycritical.Services>
      (jml.javax.safetycritical.Services.class, 
       new Class<?>[0], 
       new ObjectArrayIterator<Object[]>(new Object[][]{{}})));

    return new NonNullMultiIterator<jml.javax.safetycritical.Services>(iters);
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
  public Services_InstanceStrategy() {
    super(jml.javax.safetycritical.Services.class);
    setReflective(false);
    // uncomment to control the maximum reflective instantiation
    // recursion depth, 0 by default
    // setMaxRecursionDepth(0);
  }
}