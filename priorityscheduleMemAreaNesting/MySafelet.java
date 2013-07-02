package test.safetycritical.priorityscheduleMemAreaNesting;

import javax.safetycritical.MissionSequencer;
import javax.safetycritical.Safelet;

public class MySafelet implements Safelet
{ 
  
  public MissionSequencer getSequencer()
  {
    devices.Console.println("MyApp.getSequencer");
    return new MySequencer();
  }  
}
