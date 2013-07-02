package jml.vm;

import icecaptools.IcecapCVar;

class Architecture {
	static final byte X86_64 = 1;
	static final byte X86_32 = 2;
	static final byte CR16_C = 3;
	static final byte ATMEGA2560 = 4;

	@IcecapCVar
	static byte architecture;
}
