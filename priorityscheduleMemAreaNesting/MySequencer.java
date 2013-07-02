package test.safetycritical.priorityscheduleMemAreaNesting;

import javax.safetycritical.Mission;
import javax.safetycritical.MissionSequencer;
import javax.safetycritical.PriorityParameters;
import javax.safetycritical.StorageParameters;
import javax.scj.util.Priorities;
import javax.scj.util.Const;

public class MySequencer extends MissionSequencer
{
  private Mission mission;
  
  public MySequencer()
  {
    super (new PriorityParameters (Priorities.SEQUENCER_PRIORITY), 
           new StorageParameters (Const.PRIVATE_MEM_SIZE, 
           new long[]{Const.SCOPED_MEM_SIZE})); // mission memory size
    
    mission = new MyMission(this); 
  }
  
  public Mission getNextMission() 
  {
    if (mission.terminationPending())
    {
      devices.Console.println("\nMySeq.getNextMission:null \n"); 
      return null;
    }
    else
    {
      devices.Console.println("\nMySeq.getNextMission "); 
      return mission;
    }
  } 
}