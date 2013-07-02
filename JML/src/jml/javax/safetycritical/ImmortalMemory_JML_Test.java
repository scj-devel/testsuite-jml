/*
 * Test Oracle Class for jml.javax.safetycritical.ImmortalMemory
 * For Use With JML4 RAC
 *
 * Generated by JMLUnitNG 1.3 (103), 2013-06-16 15:01 +0200.
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

import jml.javax.safetycritical.ImmortalMemory_JML_Data.*;


/**
 * Test oracles generated by JMLUnitNG for JML4 RAC of class
 * jml.javax.safetycritical.ImmortalMemory.
 * 
 * @author JMLUnitNG 1.3 (103)
 * @version 2013-06-16 15:01 +0200
 */

public class ImmortalMemory_JML_Test {
  /**
   * The main method. Allows the tests to be run without a testng.xml or
   * the use of the TestNG executable/plugin.
   *
   * @param the_args Command line arguments, ignored.
   */
  public static void main(String[] the_args) {
    final TestNG testng_runner = new TestNG();
    final Class<?>[] classes = {ImmortalMemory_JML_Test.class};
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
    (JMLChecker.isRACCompiled(jml.javax.safetycritical.ImmortalMemory.class),
     "JMLUnitNG tests can only run on RAC-compiled code.");
  } 

  /**
   * A test for a constructor.
   *
   * @param sizeOfArea The int to be passed.
   */
  @Test(dependsOnMethods = { "test_racEnabled" }, 
        dataProvider = "p_ImmortalMemory__int_sizeOfArea__0")
  public void test_ImmortalMemory__int_sizeOfArea__0
  (final int sizeOfArea) {
    try {
      new jml.javax.safetycritical.ImmortalMemory(sizeOfArea);
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
   * A test for method instance.
   *
   * @param the_test_object The ImmortalMemory to call the test method on.
   */
  @Test(dependsOnMethods = { "test_racEnabled" })
  public void test_static_instance__0
  ( ) {
    try {
      jml.javax.safetycritical.ImmortalMemory.instance();
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
   * Data provider for constructor ImmortalMemory(int).
   * @return An iterator over strategies to use for parameter generation.
   */
  @SuppressWarnings({"unchecked"})
  @DataProvider(name = "p_ImmortalMemory__int_sizeOfArea__0", 
                parallel = false)
  public static IteratorWrapper<Object[]> p_ImmortalMemory__int_sizeOfArea__0() {
    return new IteratorWrapper<Object[]>
    (new ParameterArrayIterator
         (ImmortalMemory__int_sizeOfArea__0__sizeOfArea.class));
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
    (new ParameterArrayIterator(ImmortalMemory_InstanceStrategy.class));
  }
}