/**************************************************************************
 * File name  : MyAppTestCase.java
 *
 * This code is available under the license:
 * Creative Commons, http://creativecommons.org/licenses/by-nc-nd/3.0/
 * It is free for non-commercial use.
 *
 * VIA University College, Horsens, Denmark, 2013
 * Hans Soendergaard, hso@viauc.dk
 *
 * Description:
 *
 * Revision history:
 *   date   init  comment
 *
 *************************************************************************/

package test.safetycritical.priorityscheduleMemAreaNesting;

import javax.safetycritical.Launcher;
import javax.scj.util.Const;

import unitTest.TestCase;
import unitTest.TestResult;

public class MyAppTestCase extends TestCase
{

  public MyAppTestCase(String name)
  {
    super (name);
  }

  protected void setUp () throws Exception
  {
    Const.BACKING_STORE_SIZE = Const.BACKING_STORE_SIZE_DEFAULT;
    Const.IMMORTAL_MEM_SIZE  = Const.IMMORTAL_MEM_SIZE_DEFAULT;
    Const.SCOPED_MEM_SIZE    = Const.SCOPED_MEM_SIZE_DEFAULT;
    Const.PRIVATE_MEM_SIZE   = Const.PRIVATE_MEM_SIZE_DEFAULT;
  }

  protected void tearDown () throws Exception
  {
    //devices.Console.println("tearDown");
  }

  public void testMyApp()
  {
    devices.Console.println("testMyApp begin");

    new Launcher (new MySafelet(), Const.PRIORITY_SCHEDULING);
  }

  public static void main (String[] args)
  {
    TestCase testCase = new MyAppTestCase("myAppTestCase")
    {
      public void runTest() {
        testMyApp();
      }
    };

    TestResult result = new TestResult();
    testCase.run(result);

    devices.Console.println("Test was Successful: " + result.wasSuccessful());
    devices.Console.println("Test failures:       " + result.failureCount());
    devices.Console.println("Test errors:         " + result.errorCount());
  }

}

