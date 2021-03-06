/*
 * Test Oracle Class for jml.javax.safetycritical.RelativeTime
 * For Use With JML4 RAC
 *
 * Generated by JMLUnitNG 1.3 (103), 2013-06-17 06:30 +0200.
 * (do not modify this comment, it is used by JMLUnitNG clean-up routines)
 */

package jml.javax.safetycritical;


import java.io.PrintWriter;
import java.util.ArrayList;

import org.jmlspecs.jmlunitng.iterator.IteratorWrapper;
import org.jmlspecs.jmlunitng.iterator.ParameterArrayIterator;
import org.jmlspecs.jmlunitng.testng.BasicTestListener;
import org.jmlspecs.jmlunitng.testng.PreconditionSkipException;
import org.testng.Assert;
import org.testng.TestException;
import org.testng.TestNG;
import org.testng.annotations.DataProvider;
import org.testng.annotations.Test;
import org.testng.xml.XmlSuite;

import org.jmlspecs.jml4.rac.runtime.JMLAssertionError;
import org.jmlspecs.jml4.rac.runtime.JMLChecker;
import org.jmlspecs.jml4.rac.runtime.JMLEntryPreconditionError;
import org.jmlspecs.jml4.rac.runtime.JMLEvaluationError;

import jml.javax.safetycritical.RelativeTime_JML_Data.*;


/**
 * Test oracles generated by JMLUnitNG for JML4 RAC of class
 * jml.javax.safetycritical.RelativeTime.
 * 
 * @author JMLUnitNG 1.3 (103)
 * @version 2013-06-17 06:30 +0200
 */

public class RelativeTime_JML_Test {
  /**
   * The main method. Allows the tests to be run without a testng.xml or
   * the use of the TestNG executable/plugin.
   *
   * @param the_args Command line arguments, ignored.
   */
  public static void main(String[] the_args) {
    final TestNG testng_runner = new TestNG();
    final Class<?>[] classes = {RelativeTime_JML_Test.class};
    final BasicTestListener listener =
      new BasicTestListener(new PrintWriter(System.out));
    testng_runner.setUseDefaultListeners(false);
    testng_runner.setXmlSuites(new ArrayList<XmlSuite>());
    testng_runner.setTestClasses(classes);
    testng_runner.addListener(listener);
    testng_runner.run();
  }

  /** 
   * A test to ensure that RAC is enabled before running other tests.
   */
  @Test
  public void test_racEnabled() {
    Assert.assertTrue
    (JMLChecker.isRACCompiled(jml.javax.safetycritical.RelativeTime.class),
     "JMLUnitNG tests can only run on RAC-compiled code.");
  } 

  /**
   * A test for a constructor.
   *
   * @param millis The long to be passed.
   * @param nanos The int to be passed.
   * @param clock The Clock to be passed.
   */
  @Test(dependsOnMethods = { "test_racEnabled" }, 
        dataProvider = "p_RelativeTime__long_millis__int_nanos__Clock_clock__25")
  public void test_RelativeTime__long_millis__int_nanos__Clock_clock__25
  (final long millis, final int nanos, final jml.javax.safetycritical.Clock clock) {
    try {
      new jml.javax.safetycritical.RelativeTime(millis, nanos, clock);
    }
    catch (final JMLEntryPreconditionError $e) {
      // meaningless test
      throw new PreconditionSkipException($e.getMessage());
    }
    catch (final JMLEvaluationError $e) {
      if ($e.getCause() instanceof JMLEntryPreconditionError) {
        // meaningless test
        throw new PreconditionSkipException($e.getCause().getMessage());
      } else {
        // failed test
        throw new TestException($e.getCause().getMessage());
      }
    }
    catch (final JMLAssertionError $e) {
      // test failure
      throw new TestException($e.getMessage());
    }
    catch (final Throwable $e) {
      // test failure for some reason other than assertion violation
      throw new TestException($e.getMessage());
    }
  }

  /**
   * A test for method add.
   *
   * @param the_test_object The RelativeTime to call the test method on.
   * @param millis The long to be passed.
   * @param nanos The int to be passed.
   * @param dest The RelativeTime to be passed.
   */
  @Test(dependsOnMethods = { "test_racEnabled" }, 
        dataProvider = "p_add__long_millis__int_nanos__RelativeTime_dest__25")
  public void test_add__long_millis__int_nanos__RelativeTime_dest__25
  (final jml.javax.safetycritical.RelativeTime the_test_object, 
   final long millis, final int nanos, final jml.javax.safetycritical.RelativeTime dest) {
      if (the_test_object == null) {
        throw new PreconditionSkipException
        ("could not construct an object to test");
      }
    try {
      the_test_object.add(millis, nanos, dest);
    }
    catch (final JMLEntryPreconditionError $e) {
      // meaningless test
      throw new PreconditionSkipException($e.getMessage());
    }
    catch (final JMLEvaluationError $e) {
      if ($e.getCause() instanceof JMLEntryPreconditionError) {
        // meaningless test
        throw new PreconditionSkipException($e.getCause().getMessage());
      } else {
        // failed test
        throw new TestException($e.getCause().getMessage());
      }
    }
    catch (final JMLAssertionError $e) {
      // test failure
      throw new TestException($e.getMessage());
    }
    catch (final Throwable $e) {
      // test failure for some reason other than assertion violation
      throw new TestException($e.getMessage());
    }
  }

  /**
   * A test for a constructor.
   *
   */
  @Test(dependsOnMethods = { "test_racEnabled" })
  public void test_RelativeTime__0
  () {
    try {
      new jml.javax.safetycritical.RelativeTime();
    }
    catch (final JMLEntryPreconditionError $e) {
      // meaningless test
      throw new PreconditionSkipException($e.getMessage());
    }
    catch (final JMLEvaluationError $e) {
      if ($e.getCause() instanceof JMLEntryPreconditionError) {
        // meaningless test
        throw new PreconditionSkipException($e.getCause().getMessage());
      } else {
        // failed test
        throw new TestException($e.getCause().getMessage());
      }
    }
    catch (final JMLAssertionError $e) {
      // test failure
      throw new TestException($e.getMessage());
    }
    catch (final Throwable $e) {
      // test failure for some reason other than assertion violation
      throw new TestException($e.getMessage());
    }
  }

  /**
   * A test for a constructor.
   *
   * @param clock The Clock to be passed.
   */
  @Test(dependsOnMethods = { "test_racEnabled" }, 
        dataProvider = "p_RelativeTime__Clock_clock__25")
  public void test_RelativeTime__Clock_clock__25
  (final jml.javax.safetycritical.Clock clock) {
    try {
      new jml.javax.safetycritical.RelativeTime(clock);
    }
    catch (final JMLEntryPreconditionError $e) {
      // meaningless test
      throw new PreconditionSkipException($e.getMessage());
    }
    catch (final JMLEvaluationError $e) {
      if ($e.getCause() instanceof JMLEntryPreconditionError) {
        // meaningless test
        throw new PreconditionSkipException($e.getCause().getMessage());
      } else {
        // failed test
        throw new TestException($e.getCause().getMessage());
      }
    }
    catch (final JMLAssertionError $e) {
      // test failure
      throw new TestException($e.getMessage());
    }
    catch (final Throwable $e) {
      // test failure for some reason other than assertion violation
      throw new TestException($e.getMessage());
    }
  }

  /**
   * A test for method subtract.
   *
   * @param the_test_object The RelativeTime to call the test method on.
   * @param time The RelativeTime to be passed.
   * @param dest The RelativeTime to be passed.
   */
  @Test(dependsOnMethods = { "test_racEnabled" }, 
        dataProvider = "p_subtract__RelativeTime_time__RelativeTime_dest__50")
  public void test_subtract__RelativeTime_time__RelativeTime_dest__50
  (final jml.javax.safetycritical.RelativeTime the_test_object, 
   final jml.javax.safetycritical.RelativeTime time, final jml.javax.safetycritical.RelativeTime dest) {
      if (the_test_object == null) {
        throw new PreconditionSkipException
        ("could not construct an object to test");
      }
    try {
      the_test_object.subtract(time, dest);
    }
    catch (final JMLEntryPreconditionError $e) {
      // meaningless test
      throw new PreconditionSkipException($e.getMessage());
    }
    catch (final JMLEvaluationError $e) {
      if ($e.getCause() instanceof JMLEntryPreconditionError) {
        // meaningless test
        throw new PreconditionSkipException($e.getCause().getMessage());
      } else {
        // failed test
        throw new TestException($e.getCause().getMessage());
      }
    }
    catch (final JMLAssertionError $e) {
      // test failure
      throw new TestException($e.getMessage());
    }
    catch (final Throwable $e) {
      // test failure for some reason other than assertion violation
      throw new TestException($e.getMessage());
    }
  }

  /**
   * A test for method subtract.
   *
   * @param the_test_object The RelativeTime to call the test method on.
   * @param time The RelativeTime to be passed.
   */
  @Test(dependsOnMethods = { "test_racEnabled" }, 
        dataProvider = "p_subtract__RelativeTime_time__25")
  public void test_subtract__RelativeTime_time__25
  (final jml.javax.safetycritical.RelativeTime the_test_object, 
   final jml.javax.safetycritical.RelativeTime time) {
      if (the_test_object == null) {
        throw new PreconditionSkipException
        ("could not construct an object to test");
      }
    try {
      the_test_object.subtract(time);
    }
    catch (final JMLEntryPreconditionError $e) {
      // meaningless test
      throw new PreconditionSkipException($e.getMessage());
    }
    catch (final JMLEvaluationError $e) {
      if ($e.getCause() instanceof JMLEntryPreconditionError) {
        // meaningless test
        throw new PreconditionSkipException($e.getCause().getMessage());
      } else {
        // failed test
        throw new TestException($e.getCause().getMessage());
      }
    }
    catch (final JMLAssertionError $e) {
      // test failure
      throw new TestException($e.getMessage());
    }
    catch (final Throwable $e) {
      // test failure for some reason other than assertion violation
      throw new TestException($e.getMessage());
    }
  }

  /**
   * A test for a constructor.
   *
   * @param millis The long to be passed.
   * @param nanos The int to be passed.
   */
  @Test(dependsOnMethods = { "test_racEnabled" }, 
        dataProvider = "p_RelativeTime__long_millis__int_nanos__0")
  public void test_RelativeTime__long_millis__int_nanos__0
  (final long millis, final int nanos) {
    try {
      new jml.javax.safetycritical.RelativeTime(millis, nanos);
    }
    catch (final JMLEntryPreconditionError $e) {
      // meaningless test
      throw new PreconditionSkipException($e.getMessage());
    }
    catch (final JMLEvaluationError $e) {
      if ($e.getCause() instanceof JMLEntryPreconditionError) {
        // meaningless test
        throw new PreconditionSkipException($e.getCause().getMessage());
      } else {
        // failed test
        throw new TestException($e.getCause().getMessage());
      }
    }
    catch (final JMLAssertionError $e) {
      // test failure
      throw new TestException($e.getMessage());
    }
    catch (final Throwable $e) {
      // test failure for some reason other than assertion violation
      throw new TestException($e.getMessage());
    }
  }

  /**
   * A test for method add.
   *
   * @param the_test_object The RelativeTime to call the test method on.
   * @param time The RelativeTime to be passed.
   */
  @Test(dependsOnMethods = { "test_racEnabled" }, 
        dataProvider = "p_add__RelativeTime_time__25")
  public void test_add__RelativeTime_time__25
  (final jml.javax.safetycritical.RelativeTime the_test_object, 
   final jml.javax.safetycritical.RelativeTime time) {
      if (the_test_object == null) {
        throw new PreconditionSkipException
        ("could not construct an object to test");
      }
    try {
      the_test_object.add(time);
    }
    catch (final JMLEntryPreconditionError $e) {
      // meaningless test
      throw new PreconditionSkipException($e.getMessage());
    }
    catch (final JMLEvaluationError $e) {
      if ($e.getCause() instanceof JMLEntryPreconditionError) {
        // meaningless test
        throw new PreconditionSkipException($e.getCause().getMessage());
      } else {
        // failed test
        throw new TestException($e.getCause().getMessage());
      }
    }
    catch (final JMLAssertionError $e) {
      // test failure
      throw new TestException($e.getMessage());
    }
    catch (final Throwable $e) {
      // test failure for some reason other than assertion violation
      throw new TestException($e.getMessage());
    }
  }

  /**
   * A test for method add.
   *
   * @param the_test_object The RelativeTime to call the test method on.
   * @param millis The long to be passed.
   * @param nanos The int to be passed.
   */
  @Test(dependsOnMethods = { "test_racEnabled" }, 
        dataProvider = "p_add__long_millis__int_nanos__0")
  public void test_add__long_millis__int_nanos__0
  (final jml.javax.safetycritical.RelativeTime the_test_object, 
   final long millis, final int nanos) {
      if (the_test_object == null) {
        throw new PreconditionSkipException
        ("could not construct an object to test");
      }
    try {
      the_test_object.add(millis, nanos);
    }
    catch (final JMLEntryPreconditionError $e) {
      // meaningless test
      throw new PreconditionSkipException($e.getMessage());
    }
    catch (final JMLEvaluationError $e) {
      if ($e.getCause() instanceof JMLEntryPreconditionError) {
        // meaningless test
        throw new PreconditionSkipException($e.getCause().getMessage());
      } else {
        // failed test
        throw new TestException($e.getCause().getMessage());
      }
    }
    catch (final JMLAssertionError $e) {
      // test failure
      throw new TestException($e.getMessage());
    }
    catch (final Throwable $e) {
      // test failure for some reason other than assertion violation
      throw new TestException($e.getMessage());
    }
  }

  /**
   * A test for method add.
   *
   * @param the_test_object The RelativeTime to call the test method on.
   * @param time The RelativeTime to be passed.
   * @param dest The RelativeTime to be passed.
   */
  @Test(dependsOnMethods = { "test_racEnabled" }, 
        dataProvider = "p_add__RelativeTime_time__RelativeTime_dest__50")
  public void test_add__RelativeTime_time__RelativeTime_dest__50
  (final jml.javax.safetycritical.RelativeTime the_test_object, 
   final jml.javax.safetycritical.RelativeTime time, final jml.javax.safetycritical.RelativeTime dest) {
      if (the_test_object == null) {
        throw new PreconditionSkipException
        ("could not construct an object to test");
      }
    try {
      the_test_object.add(time, dest);
    }
    catch (final JMLEntryPreconditionError $e) {
      // meaningless test
      throw new PreconditionSkipException($e.getMessage());
    }
    catch (final JMLEvaluationError $e) {
      if ($e.getCause() instanceof JMLEntryPreconditionError) {
        // meaningless test
        throw new PreconditionSkipException($e.getCause().getMessage());
      } else {
        // failed test
        throw new TestException($e.getCause().getMessage());
      }
    }
    catch (final JMLAssertionError $e) {
      // test failure
      throw new TestException($e.getMessage());
    }
    catch (final Throwable $e) {
      // test failure for some reason other than assertion violation
      throw new TestException($e.getMessage());
    }
  }

  /**
   * A test for a constructor.
   *
   * @param time The RelativeTime to be passed.
   */
  @Test(dependsOnMethods = { "test_racEnabled" }, 
        dataProvider = "p_RelativeTime__RelativeTime_time__25")
  public void test_RelativeTime__RelativeTime_time__25
  (final jml.javax.safetycritical.RelativeTime time) {
    try {
      new jml.javax.safetycritical.RelativeTime(time);
    }
    catch (final JMLEntryPreconditionError $e) {
      // meaningless test
      throw new PreconditionSkipException($e.getMessage());
    }
    catch (final JMLEvaluationError $e) {
      if ($e.getCause() instanceof JMLEntryPreconditionError) {
        // meaningless test
        throw new PreconditionSkipException($e.getCause().getMessage());
      } else {
        // failed test
        throw new TestException($e.getCause().getMessage());
      }
    }
    catch (final JMLAssertionError $e) {
      // test failure
      throw new TestException($e.getMessage());
    }
    catch (final Throwable $e) {
      // test failure for some reason other than assertion violation
      throw new TestException($e.getMessage());
    }
  }

  /**
   * Data provider for constructor RelativeTime(long, int, Clock).
   * @return An iterator over strategies to use for parameter generation.
   */
  @SuppressWarnings({"unchecked"})
  @DataProvider(name = "p_RelativeTime__long_millis__int_nanos__Clock_clock__25", 
                parallel = false)
  public static IteratorWrapper<Object[]> p_RelativeTime__long_millis__int_nanos__Clock_clock__25() {
    return new IteratorWrapper<Object[]>
    (new ParameterArrayIterator
         (RelativeTime__long_millis__int_nanos__Clock_clock__25__millis.class,
          RelativeTime__long_millis__int_nanos__Clock_clock__25__nanos.class,
          RelativeTime__long_millis__int_nanos__Clock_clock__25__clock.class));
  }


  /**
   * Data provider for method jml.javax.safetycritical.RelativeTime add(long, int, RelativeTime).
   * @return An iterator over strategies to use for parameter generation.
   */
  @SuppressWarnings({"unchecked"})
  @DataProvider(name = "p_add__long_millis__int_nanos__RelativeTime_dest__25", 
                parallel = false)
  public static IteratorWrapper<Object[]> p_add__long_millis__int_nanos__RelativeTime_dest__25() {
    return new IteratorWrapper<Object[]>
    (new ParameterArrayIterator
         (RelativeTime_InstanceStrategy.class,
          add__long_millis__int_nanos__RelativeTime_dest__25__millis.class,
                  add__long_millis__int_nanos__RelativeTime_dest__25__nanos.class,
                  add__long_millis__int_nanos__RelativeTime_dest__25__dest.class));
  }



  /**
   * Data provider for constructor RelativeTime(Clock).
   * @return An iterator over strategies to use for parameter generation.
   */
  @SuppressWarnings({"unchecked"})
  @DataProvider(name = "p_RelativeTime__Clock_clock__25", 
                parallel = false)
  public static IteratorWrapper<Object[]> p_RelativeTime__Clock_clock__25() {
    return new IteratorWrapper<Object[]>
    (new ParameterArrayIterator
         (RelativeTime__Clock_clock__25__clock.class));
  }


  /**
   * Data provider for method jml.javax.safetycritical.RelativeTime subtract(RelativeTime, RelativeTime).
   * @return An iterator over strategies to use for parameter generation.
   */
  @SuppressWarnings({"unchecked"})
  @DataProvider(name = "p_subtract__RelativeTime_time__RelativeTime_dest__50", 
                parallel = false)
  public static IteratorWrapper<Object[]> p_subtract__RelativeTime_time__RelativeTime_dest__50() {
    return new IteratorWrapper<Object[]>
    (new ParameterArrayIterator
         (RelativeTime_InstanceStrategy.class,
          subtract__RelativeTime_time__RelativeTime_dest__50__time.class,
                  subtract__RelativeTime_time__RelativeTime_dest__50__dest.class));
  }


  /**
   * Data provider for method jml.javax.safetycritical.RelativeTime subtract(RelativeTime).
   * @return An iterator over strategies to use for parameter generation.
   */
  @SuppressWarnings({"unchecked"})
  @DataProvider(name = "p_subtract__RelativeTime_time__25", 
                parallel = false)
  public static IteratorWrapper<Object[]> p_subtract__RelativeTime_time__25() {
    return new IteratorWrapper<Object[]>
    (new ParameterArrayIterator
         (RelativeTime_InstanceStrategy.class,
          subtract__RelativeTime_time__25__time.class));
  }


  /**
   * Data provider for constructor RelativeTime(long, int).
   * @return An iterator over strategies to use for parameter generation.
   */
  @SuppressWarnings({"unchecked"})
  @DataProvider(name = "p_RelativeTime__long_millis__int_nanos__0", 
                parallel = false)
  public static IteratorWrapper<Object[]> p_RelativeTime__long_millis__int_nanos__0() {
    return new IteratorWrapper<Object[]>
    (new ParameterArrayIterator
         (RelativeTime__long_millis__int_nanos__0__millis.class,
          RelativeTime__long_millis__int_nanos__0__nanos.class));
  }


  /**
   * Data provider for method jml.javax.safetycritical.RelativeTime add(RelativeTime).
   * @return An iterator over strategies to use for parameter generation.
   */
  @SuppressWarnings({"unchecked"})
  @DataProvider(name = "p_add__RelativeTime_time__25", 
                parallel = false)
  public static IteratorWrapper<Object[]> p_add__RelativeTime_time__25() {
    return new IteratorWrapper<Object[]>
    (new ParameterArrayIterator
         (RelativeTime_InstanceStrategy.class,
          add__RelativeTime_time__25__time.class));
  }


  /**
   * Data provider for method jml.javax.safetycritical.RelativeTime add(long, int).
   * @return An iterator over strategies to use for parameter generation.
   */
  @SuppressWarnings({"unchecked"})
  @DataProvider(name = "p_add__long_millis__int_nanos__0", 
                parallel = false)
  public static IteratorWrapper<Object[]> p_add__long_millis__int_nanos__0() {
    return new IteratorWrapper<Object[]>
    (new ParameterArrayIterator
         (RelativeTime_InstanceStrategy.class,
          add__long_millis__int_nanos__0__millis.class,
                  add__long_millis__int_nanos__0__nanos.class));
  }


  /**
   * Data provider for method jml.javax.safetycritical.RelativeTime add(RelativeTime, RelativeTime).
   * @return An iterator over strategies to use for parameter generation.
   */
  @SuppressWarnings({"unchecked"})
  @DataProvider(name = "p_add__RelativeTime_time__RelativeTime_dest__50", 
                parallel = false)
  public static IteratorWrapper<Object[]> p_add__RelativeTime_time__RelativeTime_dest__50() {
    return new IteratorWrapper<Object[]>
    (new ParameterArrayIterator
         (RelativeTime_InstanceStrategy.class,
          add__RelativeTime_time__RelativeTime_dest__50__time.class,
                  add__RelativeTime_time__RelativeTime_dest__50__dest.class));
  }


  /**
   * Data provider for constructor RelativeTime(RelativeTime).
   * @return An iterator over strategies to use for parameter generation.
   */
  @SuppressWarnings({"unchecked"})
  @DataProvider(name = "p_RelativeTime__RelativeTime_time__25", 
                parallel = false)
  public static IteratorWrapper<Object[]> p_RelativeTime__RelativeTime_time__25() {
    return new IteratorWrapper<Object[]>
    (new ParameterArrayIterator
         (RelativeTime__RelativeTime_time__25__time.class));
  }


  /**
   * Data provider for methods with no parameters.
   * @return An iterator over the main class strategy.
   */
  @SuppressWarnings({"unchecked"})
  @DataProvider(name = "p_instance_only", 
                parallel = false)
  public static IteratorWrapper<Object[]> p_instance_only() {
    return new IteratorWrapper<Object[]>
    (new ParameterArrayIterator(RelativeTime_InstanceStrategy.class));
  }
}