/**************************************************************************
 * File name  : MemoryArea.java
 * 
 * This file is part of our SCJ Level 0 and Level 1 implementation, 
 * based on SCJ Draft, Version 0.79. 16 May 2011.
 *
 * It is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as  
 * published by the Free Software Foundation, either version 3 of the 
 * License, or (at your option) any later version.
 *
 * This SCJ Level 0 and Level 1 implementation is distributed in the hope 
 * that it will be useful, but WITHOUT ANY WARRANTY; without even the  
 * implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  
 * See the GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this SCJ Level 0 and Level 1 implementation.  
 * If not, see <http://www.gnu.org/licenses/>.
 *
 * Copyright 2012 
 * @authors  Anders P. Ravn, Aalborg University, DK
 *           Stephan E. Korsholm and Hans S&oslash;ndergaard, 
 *             VIA University College, DK
 *   
 * Description: 
 * 
 * Revision history:
 *   date   init  comment
 *
 *************************************************************************/

package jml.javax.safetycritical;

//import java.lang.reflect.Array;

import jml.javax.safetycritical.annotate.Level;
import jml.javax.safetycritical.annotate.SCJAllowed;
import jml.javax.scj.util.Const;

//import reflect.ObjectInfo;
import jml.vm.Memory;

/**
 * All allocation contexts are implemented by memory areas. This is the
 * base-level class for all memory areas.
 * 
 * @version 1.0; - May 2012
 * 
 * @author Anders P. Ravn, Aalborg University, <A
 *         HREF="mailto:apr@cs.aau.dk">apr@cs.aau.dk</A>, <br>
 *         Hans S&oslash;ndergaard, VIA University College, Denmark, <A
 *         HREF="mailto:hso@viauc.dk">hso@viauc.dk</A>
 * 
 * @scjComment - semantic issue: <code>MemoryArea</code> is part of an
 *             infrastructure. It should not be accessible to applications. At
 *             least it should be tagged INFRASTRUCTURE.
 *             <p>
 *             - implementation issue: Omitted the following methods:
 *             <ul>
 *             <code>  
 *     <li>public static MemoryArea getMemoryArea(java.lang.Object object) 
 *     <li>public Object newArray (Class type, int number) 
 *     <li>public Object newInstance (Class type) 
 *    </code>
 *             </ul>
 */

@SCJAllowed(Level.INFRASTRUCTURE)
public class MemoryArea implements AllocationContext {

	/** Singleton reference for the immortal memory. */
	protected static MemoryArea head;
	protected static MemoryArea currentActiveArea = null;

	protected static int backingStoreEnd;
	protected static int backingStoreBase;

	Memory delegate;
	
	private MemoryArea next;
	private int memLevel;    // Immortal has level 0; 
                           // MissSeq private mem: 1; MissSeq mission mem: 2; 
                           // Idle handler mem: 3
                           // Handlers private mem: >= 4;	
	
	static int memoryLevel = Const.IMMORTAL_MEM_LEVEL; 
	
	/*@ 
    public invariant 
      size() == memoryConsumed() + memoryRemaining();       
    @*/
	
	/**
	 * Creates a new memory area.
	 * @param size The size of this new memory area.
	 */
	/*@ 
	  behavior    
      requires size > 0;   
      ensures size() == size && memoryConsumed() == 0;
    @*/
	MemoryArea(int size) {
		int base = getBase();
		if (base + size < backingStoreEnd) {
			delegate = new Memory(base, size);
			next = null;
			memLevel = memoryLevel++;
		} else {
			base = base - head.delegate.getBase();
			//devices.Console.println("Out of backingstore: " + base + ", " + (base + size) + ", " + (backingStoreEnd - head.delegate.getBase()));
		}
		linkMemoryArea(this);
	}

	private static int getBase() {
		MemoryArea current = head;
		int base = backingStoreBase;
		while (current != null) {
			int currentEnd = current.delegate.getBase() + current.delegate.getSize();
			if (currentEnd > base) {
				base = currentEnd;
			}
			current = current.next;
		}
		return base;
	}

	private static void linkMemoryArea(MemoryArea memoryArea) {
		if (head == null) {
			head = memoryArea;
		} else {
			MemoryArea current = head;
			while (current.next != null) {
				current = current.next;
			}
			current.next = memoryArea;
		}
	}

	// HSO: 13June2013: public just now,
	// else: private /*@ spec_public @*/

	/*@ 
	  public behavior    
      requires true;   
      ensures \result >= 0 && unchanged();
    @*/
	public int getMemoryAreaLevel()
	{
		return memLevel;
	}
	
	private static int getScopeIndex(Object object)
	{
	  int index = 0;
	  MemoryArea current = head;
	  while (current != null) 
	  {
		  index++;
		  if (current != getMemoryArea(object))
		  {
			  current = current.next;
		  }
		  else
			  break;
	  }
	  return index;
	}
	
	private static MemoryArea[] toArray (Object object)
	{
		MemoryArea[] arr = new MemoryArea[getScopeIndex(object)];
		int i = 0;
		MemoryArea current = head;
		while (current != null) 
		{
			arr[i] = current;
			if (current != getMemoryArea(object))
			{
				current = current.next;
				i++;
			}
			else
			  break;
		  }	
		 //devices.Console.println("MemoryArea.toArray length: " + arr.length);
		 return arr;
	}
	
	// HSO: 17June2013: public just now, - for test; 
	// else should be: private /*@ spec_public @*/
	public static MemoryArea[] getContexts (Object object)
	{
		MemoryArea[] scopeStack = toArray (object);
		//devices.Console.println("1 MemoryArea.getContexts: size: " + scopeStack.length);
//		for (int i = 0; i < scopeStack.length; i++)
//		{
//		  MemoryArea area = scopeStack[i];  
//		  //devices.Console.println("2 MemoryArea.getContexts, level: " + area.memLevel);
//		}
		return scopeStack;
	}

		
	// HSO: 30Jan2013
	void removeArea() {
		if (this != head) {
			MemoryArea current = head;
			while (current.next != this) {
				current = current.next;
			}
			current.next = next;
		}
		// int offset = this.delegate.getBase() - immortal.delegate.getBase();
		// int size = this.delegate.getSize();
		// devices.Console.println("-: [" + offset + " -> " + (offset + size) +
		// "] [" + size + "]");
	}

	/**
	 * Makes this memory area the allocation context for the execution of the
	 * <code>run()</code> method of the instance of <code>Runnable</code> given
	 * in the constructor. <br>
	 * During this period of execution, this memory area becomes the default
	 * allocation context until another allocation context is selected or the
	 * <code>Runnable</code>'s <code>run</code> method exits.
	 * <p>
	 * This method is like the <code>executeInArea</code> method, but extended
	 * with cleanup and pointer reset.
	 * 
	 * @throws IllegalArgumentException
	 *             Thrown if the caller is a schedulable object and
	 *             <code>logic</code> is null.
	 * 
	 * @param logic
	 *            The <code>Runnable</code> object whose <code>run()</code>
	 *            method shall be executed.
	 */
	@SCJAllowed(Level.INFRASTRUCTURE)
	void enter(Runnable logic) throws IllegalArgumentException {
		if (logic == null)
			throw new IllegalArgumentException();

		MemoryArea outerArea = currentActiveArea;
		currentActiveArea = this;

		outerArea.delegate.switchToArea(this.delegate);

		logic.run();

		this.delegate.switchToArea(outerArea.delegate);

		this.delegate.reset();

		currentActiveArea = outerArea;
	}

	/*@ 
    behavior    
      requires true;  
      ensures memoryConsumed() == 0;      
    @*/
	void resetMemoryArea() {
		this.delegate.reset();
	}

	/**
	 * Return the memory region which we are currently in.
	 */
	static MemoryArea getCurrentMemory() 
	{
		return currentActiveArea;
	}

	/**
	 * 
	 * @scjComment Omitted, - not implemented
	 * @param object
	 *            An object.
	 * @return The memory area in which <code>object</code> is allocated.
	 */
  // Implementation commented out; 
	// reflect.ObjectInfo is not part of vm interface to HVM
	// The implementation cannot run on Eclipse VM; cannot test it here;
	/*@ 
    public behavior    
      requires object != null;  
      ensures  \result != null;  // is tested elsewhere, see Test Suite paper, section 3.3 
    @*/
	@SCJAllowed
	public static MemoryArea getMemoryArea(java.lang.Object object) {
//		int ref = ObjectInfo.getAddress(object);
//		MemoryArea current = head;
//		while (current != null) {
//			if ((current.delegate.getBase() <= ref) && (ref < current.delegate.getBase() + current.delegate.getSize())) {
//				return current;
//			}
//			current = current.next;
//		}
		return null;
	}

	/**
	 * Executes <code>logic</code> in this memory area, with no cleanup and no
	 * pointer reset at the end.
	 * 
	 * @param logic
	 *            The Runnable object whose <code>run()</code> method shall be
	 *            executed.
	 * 
	 * @throws IllegalArgumentException
	 *             If <code>logic</code> is null.
	 */
	// Not public any more in SCJ Draft
	@SCJAllowed
	public void executeInArea(Runnable logic) throws IllegalArgumentException {
		if (logic == null)
			throw new IllegalArgumentException();

		MemoryArea outerArea = currentActiveArea;
		Memory currentMemory;

		if (outerArea == null) {
			currentMemory = Memory.getCurrentAllocationArea();
		} else {
			currentMemory = outerArea.delegate;
		}

		currentActiveArea = this;

		currentMemory.switchToArea(this.delegate);

		logic.run();

		this.delegate.switchToArea(currentMemory);

		currentActiveArea = outerArea;
	}

	/**
	 * @return The memory consumed (in bytes) in this memory area.
	 */
	/*@ 
    public behavior
      requires true;     
      ensures \result >= 0 && unchanged(); 
    @*/
	@SCJAllowed
	public long memoryConsumed() {
		return (long) delegate.consumedMemory();
	}

	/**
	 * @return The memory remaining (in bytes) in this memory area.
	 */
	/*@ 
    public behavior
      requires true;    
      ensures \result == size() - memoryConsumed() && unchanged();
    @*/
	@SCJAllowed
	public long memoryRemaining() {
		return size() - memoryConsumed();
	}

	/**
	 * Creates an new array of the given type in this memory area.
	 * 
	 * @scjComment Omitted, - not tested
	 * 
	 * @param type
	 *            is the class type of objects this array should hold
	 * @param number
	 *            is the length of the array
	 * @return A new array of type <code>type</code> and length
	 *         <code>number</code>.
	 */
//	@SCJAllowed
//	public Object newArray(@SuppressWarnings("rawtypes") Class type, int number) throws IllegalArgumentException, OutOfMemoryError {
//		MemoryArea outerArea = currentActiveArea;
//		currentActiveArea = this;
//
//		outerArea.delegate.switchToArea(this.delegate);
//
//		Object array = Array.newInstance(type, number);
//
//		this.delegate.switchToArea(outerArea.delegate);
//
//		currentActiveArea = outerArea;
//		return array;
//	}

	/**
	 * Creates a new instance of the given type in this memory area.
	 * 
	 * @scjComment Omitted, - not tested
	 * 
	 * @param type
	 *            is the class type of object to be created
	 * @return An object of type <code>type</code>.
	 */
//	@SCJAllowed
//	public Object newInstance(@SuppressWarnings("rawtypes") Class type) throws IllegalAccessException, IllegalArgumentException, InstantiationException, OutOfMemoryError {
//		MemoryArea outerArea = currentActiveArea;
//		currentActiveArea = this;
//
//		outerArea.delegate.switchToArea(this.delegate);
//
//		Object object = type.newInstance();
//
//		this.delegate.switchToArea(outerArea.delegate);
//
//		currentActiveArea = outerArea;
//		return object;
//	}

	/**
	 * @return The size of the current memory area in bytes.
	 */
	/*@ 
    public behavior
      requires true;     
      ensures \result >= 0 && unchanged(); 
    @*/
	@SCJAllowed
	public long size() {
		return this.delegate.getSize();
	}

	/**
	 * Helper method for <code>ManagedMemory.enterPrivateMemory</code>
	 * 
	 * @param size
	 *            The size of inner private memory
	 * @param logic
	 *            The logic to be executed in inner private memory
	 */
	/** Inner area for enterPrivateMemory. */
	MemoryArea innerArea;

	void enterMemory(int size, Runnable logic) {
		// ToDo: resize ? + test it
		if (innerArea == null) {
			innerArea = new MemoryArea(size);
		}
		// Set all fields for inner and call enter
		innerArea.enter(logic);
		//innerArea = null; // ??
	}

	static void allocateBackingStore(int size) {
		backingStoreBase = Memory.alloc(size);

		backingStoreEnd = backingStoreBase + size;
	}
	
	private boolean unchanged()
	{
	  return delegate.unchanged();
	}
}
