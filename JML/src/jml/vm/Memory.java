package jml.vm;

//import icecaptools.IcecapCVar;
//import icecaptools.IcecapCompileMe;

//import javax.safetycritical.annotate.hvm.IcecapCompileMe;

import jml.javax.scj.util.Const;

public class Memory {
	private int base;
	private int size;
	private int free;  // consumed memory
	
	/*@ 
	  public invariant 
	    (this.getSize() >= 0) && 
	    (0 <= this.consumedMemory() && this.consumedMemory() <= this.getSize());
	  @*/

	/*@ 
	  public behavior
	    requires base >= 0 && size >= 0 && base + size <= Const.BACKING_STORE_SIZE;
      ensures this.base == base && this.size == size && this.free == 0;  
    @*/
	public Memory(int base, int size) {	
	  //System.out.println ("Memory constructor: base, size: " + base + " " + size );
		this.base = base;
		this.size = size;
		this.free = 0;
	}
	
	/*@ 
	  public behavior
	    requires newScope != null;
      ensures currentMemoryArea == newScope;
    @*/
	public void switchToArea(Memory newScope) {
		Memory newScopeArea = (Memory) newScope;
		currentMemoryArea = newScopeArea;
	}

	/*@ 
	  public behavior
	    requires 0 <= size && size <= currentMemoryArea.size - currentMemoryArea.free;
	    assignable currentMemoryArea.free;
      ensures \result ==  \old(currentMemoryArea.base) + \old(currentMemoryArea.free);
    @*/
	public static int alloc(int size) {
		if (currentMemoryArea.free + size > currentMemoryArea.size) {
			throw new OutOfMemoryError();
		}

		int startPtr = currentMemoryArea.base + currentMemoryArea.free;
		currentMemoryArea.free += size;
		return startPtr;
	}

	//private static Memory currentMemoryArea;
	
	// currentMemoryArea is instantiated by HVM through this native method:
  //private static native void registerDefaultMemoryArea(Memory defaultAllocationArea);
	
	// The next three fields are for JML and testing on Eclipse VM;
	// They replace the HVM dependent currentMemoryArea above.
	private static final  int memBase = 0;
	private static final  int memSize = Const.BACKING_STORE_SIZE;
	private static Memory currentMemoryArea = new Memory(memBase,memSize);

	/*@ 
	  public behavior
	    requires true;
      assignable \nothing;
      ensures \result == Memory.currentMemoryArea;
    @*/
	public static Memory getCurrentAllocationArea() {
		//registerDefaultMemoryArea(currentMemoryArea);
		return currentMemoryArea;
	}

	/*@ 
	  public behavior
	    requires true;
      assignable \nothing;
      ensures this.free == 0;
    @*/
  public void reset() {
		free = 0;
	}

	/*@ 
	  public behavior
	    requires true;
      assignable \nothing;
      ensures \result == this.free;
    @*/
  public int consumedMemory() {
		return free;
	}

  /*@ 
    public behavior
      requires true;
      assignable \nothing;
      ensures \result == this.base;
    @*/
  public int getBase() {
		return base;
	}

	/*@ 
	  public behavior
	    requires true;
	    assignable \nothing;
	    ensures \result == this.size;
	  @*/
  public int getSize() {
		return size;
	}
  
  /*@ 
    public behavior
      requires true;      
      assignable \nothing;
      ensures base == \old(base) && size == \old(size) && free == \old(free);
    @*/
  public boolean unchanged()
  {
    return true;
  }
}
