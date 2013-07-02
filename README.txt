
The JML specifications are added to the SCJ implementation for the HVM:
http://www.icelab.dk

To avoid name mismatch, the packages start with jml, e.g. jml.javax.safetycritical.

This JML specification should be regarded as a draft.
Not all the specifications have got their final form,
but at least the classes referred to in Section 3.2 and 3.3 in 
"A Test Suite for Safety-Critical Java using JML".

========================================================================
Using JMLUnitNG :
========================================================================

Example:
========================================================================
abstract class HighResolutionTime in package jml.javax.safetycritical; 
========================================================================

Calling jmlunitng:
$ java -jar jmlunitng.jar --package -cp jmlunitng.jar:jml4c.jar:./src src/jml/javax/safetycritical/HighResolutionTime.java

Calling jml4c:
$ java -jar jml4c.jar -cp jml4c.jar:./src src/jml/javax/safetycritical/HighResolutionTime.java


Running: in Eclipse.


========================================================================


The memory allocation contexts test, Section 3.3, is executed on the HVM.
