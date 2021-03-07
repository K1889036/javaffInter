/************************************************************************
 * Strathclyde Planning Group,
 * Department of Computer and Information Sciences,
 * University of Strathclyde, Glasgow, UK
 * http://planning.cis.strath.ac.uk/
 * 
 * Copyright 2007, Keith Halsey
 * Copyright 2008, Andrew Coles and Amanda Smith
 * Copyright 2015, David Pattison
 *
 * This file is part of JavaFF.
 * 
 * JavaFF is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 2 of the License, or
 * (at your option) any later version.
 * 
 * JavaFF is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with JavaFF.  If not, see <http://www.gnu.org/licenses/>.
 * 
 ************************************************************************/

package javaff.search;

import javaff.JavaFF;

import javaff.data.Action;
import javaff.data.Fact;
import javaff.data.GroundProblem;
import javaff.data.Plan;
import javaff.data.TimeStampedPlan;
import javaff.data.TotalOrderPlan;
import javaff.data.strips.NullFact;
import javaff.data.strips.RelaxedFFPlan;
import javaff.planning.HelpfulFilter;
import javaff.planning.NullFilter;
import javaff.planning.STRIPSState;
import javaff.planning.State;
import javaff.planning.Filter;
import javaff.JavaFF;
import javaff.data.TotalOrderPlan;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Set;
import java.util.LinkedList;
import java.util.Comparator;
import java.math.BigDecimal;

import java.util.Hashtable;
import java.util.Iterator;

import java.util.Scanner;
import java.lang.Thread;
import java.util.ArrayList;
import java.util.Arrays;

import java.util.concurrent.TimeUnit;


public class EnforcedHillClimbingSearch extends Search
{
	protected int b;
	protected BigDecimal bestHValue;
	protected BigDecimal succA;
	public static Scanner EHCScanner = new Scanner(System.in);
	protected static boolean searchStart = false;
	private static int x;
	private static int y;
	protected static int z;
	private static State c;
	public static long startAction;
	public static long endAction;
	public static long overallAction;
	//HAFAS
	//huh
	public static long newOverall;
	
	protected static boolean validCMD;
	protected static boolean actionPhase;
	protected static boolean searchEHC;
	
	protected static boolean showStates;
	protected static boolean showHValue;
	
	//cache the hash codes rather than the states for memory efficiency
	protected HashSet<Integer> closed;
	protected LinkedList<State> open;
	
	//protected static ArrayList<String> cmd = new ArrayList<String>();
	//protected static HashMap<ArrayList<String>,String> cmds = new HashMap<ArrayList<String>, String>();

	public EnforcedHillClimbingSearch(State s)
	{
		this(s, new HValueComparator());
	}

	public EnforcedHillClimbingSearch(State s, Comparator c)
	{
		super(s);
		setComparator(c);

		closed = new HashSet<Integer>();
		open = new LinkedList<State>();
	}

	public void setFilter(Filter f)
	{
		filter = f;
	}

	public State removeNext()
	{

		return (State) (open).removeFirst();
	}

	public boolean needToVisit(State s)
	{
		if (closed.contains(s.hashCode()))
			return false;

		closed.add(s.hashCode()); // otherwise put it on
		return true; // and return true
	}

	public State search()
	{
		System.out.println("Each commands do something different and some are applicable only at specific time of the search. If you are unsure of what any of these commands do type: cmds"
				+ "\nIt will give you information on what each commands do and when they are applicable.\n"
				+"To get the currently applicable commands type: help \n"
				+"It can be used at any stage of the search\n"+
				"\nThe available commands are: help, info, cmds, lim, search, limit, BFS, goal");

		if (start.goalReached())
		{ // wishful thinking
			return start;
		}
		searchStart = true;
		searchEHC = true;
		//System.out.println("it is YYYY " + y);
		startAction = System.nanoTime();
		controlCMD();
		endAction= System.nanoTime();
		overallAction = endAction - startAction;
		newOverall = newOverall + overallAction;
		System.out.println("its overall: " + newOverall/1000000000);
		System.out.println("Performing search using EHC with standard helpful action filter");
		if(searchEHC==true) {

			needToVisit(start); // dummy call (adds start to the list of 'closed'
								// states so we don't visit it again
	
			open.add(start); // add it to the open list
			bestHValue = start.getHValue(); // and take its heuristic value as the
											// best so far
	
			javaff.JavaFF.infoOutput.print(bestHValue+" into depth ");
			int statesEvaluated = 1;
			int statesEvaluatedPerH = 1;
			int maxDepth = 1;
			HashMap<State, Integer> successorLayers = new HashMap<State, Integer>();
			successorLayers.put(start, 1);
			
			int currentDepth = 1, prevDepth = 0;
			out: while (!open.isEmpty()) // whilst still states to consider
			{
				State curr = open.pop();
				c = curr;
				//System.out.println("the alpha "+curr);
				closed.add(curr.hashCode());
				currentDepth = successorLayers.get(curr);
				if (currentDepth > maxDepth)
					maxDepth = currentDepth;
				
				if (currentDepth > prevDepth)
				{
					JavaFF.infoOutput.print("["+(currentDepth)+"]"); 
					prevDepth = currentDepth;
				}
				
				List<Action> applicable = filter.getActions(curr); //use filter to see which actions are applicable.
				in: for (Action a : applicable)
				{
					State succ = curr.getNextState(a); 
					if (this.closed.contains(succ.hashCode()) == true)
					{
						continue in;
					}
					++statesEvaluated;
					++statesEvaluatedPerH;

					BigDecimal succH = succ.getHValue();
					//check we have no entered a dead-end
					if (((STRIPSState) succ).getRelaxedPlan() == null)
						continue;
					
					//now do online goal-ordering check -- this is used by FF to prevent deleting goals early in the 
					//relaxed plan, which would then need negated again later on
					boolean threatensGoal = this.isGoalThreatened(((STRIPSState) succ).getRelaxedPlan(), succ.goal);
					if (threatensGoal)
					{
	//					closed.add(succ); //The real FF says that this state should be "removed" from the state-space -- we just skip it
						continue; //skip successor state
					}
					
					if (succ.goalReached())
					{ // if we've found a goal state -
						// return it as the
						// solution
						JavaFF.infoOutput.println("\nEvaluated "+statesEvaluated+" states to a max depth of "+maxDepth);
						
						return succ;
					}
					else if (succH.compareTo(bestHValue) < 0)
					{
						// if we've found a state with a better heuristic
						// value
						// than the best seen so far
						
						bestHValue = succH; // note the new best value
						open.clear();
						open.add(succ); // add it to the open list
						successorLayers.clear();
						successorLayers.put(succ, 1);
						prevDepth = 0;
						currentDepth = 1;
						statesEvaluatedPerH = 1;
						
						if(showStates==true) {
							JavaFF.infoOutput.print("\n"+"The current state is: "+ curr);
						}
						if(showHValue == true) {
							JavaFF.infoOutput.print("\n"+"states: "+ statesEvaluated);
						}
						JavaFF.infoOutput.print("\n"+bestHValue+" into depth ");
						 //TODO delete this later.
						//JavaFF.infoOutput.print("\n"+"blabla: "+ curr);
						//JavaFF.infoOutput.print("\n"+"states: "+ );
						//JavaFF.infoOutput.print("\n"+bestHValue+" into depth "+" states evaluated "+statesEvaluated);
						
						continue out; // and skip looking at the other successors
					}
					else if(statesEvaluatedPerH >= y) { //this part works to some extent but might want to improve a bit. Porblem with pf3 with 4 hvalue does not find a plan for some reason.
						System.out.println("thats y "+y +" thats seph " +statesEvaluatedPerH+"   dada "+statesEvaluated);
						System.out.println("\n" + "The limit of nodes expended "+"("+y+")"+" per heuristic value was reached for the heuristic value: "+bestHValue +"\n"+
					"The avaiable commands are: help, info, cmds, addLim, action, state");
						
						actionPhase = true;
						startAction = System.nanoTime();
						controlCMD();
						int num = 0;
						HashMap<Integer,Action> ActionMap = new HashMap<Integer,Action>();
						System.out.println("select an action to apply by typing the number linked to the action: \n");
						for(int i =0; i < applicable.size(); i++) {
							num++;
							ActionMap.put(num, applicable.get(i));
							System.out.println(num +" "+ applicable.get(i)); // prints actions
						}
						
						System.out.println("\n"+ "The current state is: "+curr);
						//searchStart = false;
						boolean valid = true;
						while(valid) {
							//startAction = System.nanoTime(); //only does it once...
							
							while(!EHCScanner.hasNextInt()) {
								EHCScanner.nextLine();
								System.out.println("The input needs to be an integer...");
							}
							int actionSelector = EHCScanner.nextInt();
								if(actionSelector <= num && actionSelector >= 1){
									EHCScanner.nextLine();
									succ = curr.getNextState(ActionMap.get(actionSelector));
									System.out.println("You have applied: "+ ActionMap.get(actionSelector));
									valid = false;
								} else {
									System.out.println("Please input a valid action...");
									EHCScanner.nextLine();
								}
						//	endAction = System.nanoTime();
							//overallAction = endAction - startAction;
							
						}
						endAction = System.nanoTime();
						overallAction = endAction - startAction;
						newOverall = newOverall + overallAction;
					//	System.out.println("its overall: " + newOverall/1000000000);
						System.out.println("actiooverall= "+newOverall/1000000000);
						open.clear();
						open.add(succ); // add it to the open list
						successorLayers.clear();
						successorLayers.put(succ, 1);
						prevDepth = 0;
						currentDepth = 1;
						statesEvaluatedPerH = 1;
						//System.out.println(statesEvaluated);
						//y = 1000; // can do something like this to change the value of y
						ActionMap.clear();
						continue out; 
					
						//System.out.println(ActionMap); // not print this.
						//System.out.println(curr);
						//System.out.println(test);
						//return curr; //if i do this i return the current path it took
						//return null; // need to do current hvalue - previous.
					}
					/*else if(statesEvaluated >= x){ // TODO fix this, it does not work when put hvalue as well.
						System.out.println("\n"+"too many states: " + statesEvaluated); // compare the states evaluated with the number the user has inputted.
							return null;
					} */
					else
					{
						open.add(succ); // add it to the open list
						successorLayers.put(succ, currentDepth + 1); //this used to be before the previous else if.
					//	System.out.println("testtt "+curr);
	//					prevDepth = currentDepth;
					}
					
					
				}
				
			}
		} else {
			return null;
		}
		return null;
	}
	
	/**
	 * Tests whether any of the actions in the RELAXED plan associated with this state
	 * delete a goal.
	 * @param relaxedPlan The relaxed plan which will be used to detect goal orderings
	 * @param goal The goal to check
	 * @return
	 */
	private boolean isGoalThreatened(Plan relaxedPlan, Fact goal)
	{
		//maintain a list of achieved goals as we go through the RP in-order. These will
		//be checked at each timestep to see if any already achieved goals are deleted.
		HashSet<Fact> achieved = new HashSet<Fact>();
		List<Action> actions = relaxedPlan.getActions();
		
		
		for (Action a : actions)
		{
			for (Fact g : goal.getFacts())
			{
				//if this action deletes a goal and that goal has already been achieved by 
				//a previous action in the RP, immediately return
				if (a.deletes(g) && achieved.contains(g))
					return true;
			}
			
			achieved.addAll(a.getAddPropositions());
			achieved.addAll(a.getDeletePropositions()); //needed for ADL goals
		}
		
		return false;
	}
	protected static void controlCMD() {
		//System.out.println((endAction));
		validCMD =true;
		while(validCMD) {
			String cmmds = EHCScanner.nextLine();
			if(cmmds.equals("continue")) {
				System.out.println("Going to search! ");
				validCMD = false;
			}	
			else if(cmmds.equals("bfs")&& searchStart == true) {
				searchEHC = false;
				searchStart = false;	
				validCMD = false;
			}
			else if(cmmds.equals("help")) {
				if((searchStart == true)&&(actionPhase == false)) {
					System.out.println("Your commands are: help, info, cmds, lim, search, limit, BFS"); 
				}
				else if((actionPhase == true) && (searchStart == false) && (BestFirstSearch.searchStartBFS == false)){
					System.out.println("The commands are: help, info, cmds, addLim, action, state");
				}
				else if((BestFirstSearch.searchStartBFS == true) && (BestFirstSearch.actionPhaseBFS == false)) {
					System.out.println("Your commands are: help, info, cmds, lim, search");
				}
				else if(BestFirstSearch.actionPhaseBFS == true && BestFirstSearch.searchStartBFS == false) {
					System.out.print("The commands are: help, info, cmds, addLim, action, state");
				}
			}
			else if(cmmds.equals("info")) {
				System.out.println("JavaFF is a planner written in Java"); // TODO make it more complete
			}
			else if(cmmds.equals("info "+"EHC")) {
				System.out.println("Info about EHC");
			}
			else if(cmmds.equals("info "+"BFS")) {
				System.out.println("Info about BFS");
			}
			else if(cmmds.equals("cmds")) {
				System.out.println(" _______________________________________________________________________________________________________________________________________________________________________________________________________\n" + 
						"|\n" + 
						"| The commands in this planner are:\n" + 
						"|\n" + 
						"| action - The action command allows the user to select an action to apply. The action command is only available when the nodes expended per heuristic value is reached. The action command can be used\n" + 
						"| during both EHC and BFS. When action is inputted, a list of all the avaialble action mapped with a unique number is displayed, to select the action to apply input the number that correspond to the \n" + 
						"| action you want to select.\n" + 
						"|\n" + 
						"| bfs - The command bfs allow the user to skip the EHC search and search directly with Best First Search. The bfs command is only usable at the start menu.\n" + 
						"|\n" + 
						"| cmds - The command cmds displays all of the existing commands for this planner with some information about all of them.\n" + 
						"|\n" + 
						"| goal - The command goal displays the goal of the problem. This command can be used at any time.\n" + 
						"|\n" + 
						"| help - The command help displays all of the available commands during each stage of the search. \n" + 
						"|\n" + 
						"| info - The command info will give information about the planner, the search algorithm used. The command info alone only displays general information about the planner JavaFF.\n" + 
						"|	info ehc - The command \"info ehc\" will display some information about the search algorithm EHC.\n" + 
						"|	info bfs - the command \"info bfs\" will display some information about the search algorithm BFS.\n" + 
						"|\n" + 
						"| limH - The command \"limH\" allow the user to put a limit of node to expend per heuristic value during the search. This command can only be used at the start of EHC and the start of BFS.\n" + 
						"|	addLim - The command \"addLim\" allow the user to change the limit of nodes to expend per heuristic value midway throught the search. This command is only usable during the search.\n" + 
						"|\n" + 
						"| manual - The command \"manual\" will set the limit of nodes to expend per heuristic value to 1. It will still search until the limit is reached, but it will ask the user to prompt nearly every action\n" + 
						"| it needs to take.\n" + 
						"|\n" + 
						"| nonApplicable - the command \"nonApplicable\" allow the user to see all of the non applicable action for the state he is currently in. This command is only used during the BFS search. \n" + 
						"|\n" + 
						"| search - The command \"search\" can only be used at the start of EHC and BFS. When the command \"search\" is inputed, the search begins. If the command \"limH\" was not specified prior to using \"search\" \n" + 
						"| then it will search until it finds a solution to the problem.\n" + 
						"|\n" + 
						"| show - The command \"show\" allow the user to get a better look of what is happening during the search. There are different variation:\n" + 
						"|	show states - The command \"show states\" will show the different states that are explored during the search.\n" + 
						"|	show nodes - The command \"show nodes\" will show the total amount of nodes expended per states. \n" + 
						"|\n" + 
						"| state - The command \"state\" will display the current state. This command is only usable during the search. \n" + 
						"|");
			}
			else if((searchStart == true) && (cmmds.equals("limit"))) {
				System.out.println("Select a limit of state to expend: ");
				control();
				x = EHCScanner.nextInt();
				System.out.println("You have selected to set the limit to: "+x);
			}
			else if(cmmds.equals("limH")&&(BestFirstSearch.searchStartBFS == true)&&(searchStart == false)) {
				System.out.println("Select limit pls: .. ");
				control();
				z = EHCScanner.nextInt();
				System.out.println("you have set the limit to: "+z);
			}
			else if((cmmds.equals("limH"))&&(searchStart == true)&&(BestFirstSearch.searchStartBFS == false)) {
				System.out.println("Select a limit of state to expend per Hvalue");
				control();
				y = EHCScanner.nextInt();
				System.out.println("limit set to: "+y);
			}
			else if((cmmds.equals("addLimH"))&&(searchStart == false)&&(actionPhase == true)) {
				System.out.println("Change the limit of state to expend per Hvalue");
				control();
				y = EHCScanner.nextInt();
				System.out.println("limit set to: "+y);
			}
			else if((cmmds.equals("addLimH"))&&(BestFirstSearch.searchStartBFS == false)&&(BestFirstSearch.actionPhaseBFS == true)) {
				System.out.println("Change the limit of nodes to expend: ");
				control();
				z = EHCScanner.nextInt();
				System.out.println("limit set to: "+z);
			}
			else if((cmmds.equals("search")) && (searchStart == true)) {
				System.out.println("Starting to search with EHC...");
				if(y==0) {
					y = 2147483647;
					System.out.println("Performing normal EHC search");
				}
				searchStart = false;
				validCMD = false;
			}
			else if((cmmds.equals("search")) && BestFirstSearch.searchStartBFS == true) {
				System.out.println("Searching with BFS...");
				if(z==0) {
					z = 2147483647;
					System.out.println("Performing normal BFS search");
				}
				BestFirstSearch.searchStartBFS = false;
				validCMD = false;
			}
			else if(cmmds.equals("state")&&(searchStart==false)&&(BestFirstSearch.searchStartBFS == false)&&(searchEHC == true)) {
				System.out.println("your current state is: "+c);
			}
			else if(cmmds.equals("state")&&(searchStart==false)&&(BestFirstSearch.searchStartBFS == false)&&(BestFirstSearch.searchBFS == true)) {
				System.out.println("Your current state is: "+BestFirstSearch.stateBFS);
			}
			else if(cmmds.equals("action")&&(actionPhase==true && BestFirstSearch.actionPhaseBFS == false)){
				actionPhase = false;
				validCMD = false;
				BestFirstSearch.test = false;
			}	
			else if(cmmds.equals("action")&& (actionPhase==false && BestFirstSearch.actionPhaseBFS == true)) {
				if(BestFirstSearch.actionPhaseBFS == true) {
					System.out.println("its on");
				}
				BestFirstSearch.actionPhaseBFS = false;
				BestFirstSearch.test= false;
				validCMD = false;
			}
			else if(cmmds.equals("notApplicable")&&(BestFirstSearch.actionPhaseBFS==true)) {
				BestFirstSearch.megaWhileBFS = true;
				validCMD = false;
				}
			else if(cmmds.equals("goal")) {
				System.out.println("The goal state is: "+JavaFF.endState);
			}
			else if(cmmds.equals("manual")&&(searchStart==true)) {
				y = 1;
			}
			else if(cmmds.equals("show"+" states")) {
				showStates = true;
			}
			else if(cmmds.equals("show"+" nodes")) {
				showHValue = true;
			}
			
		//	endAction = System.nanoTime();
			//overallAction = endAction - startAction;
			
			 
		}	
	//	newOverall = newOverall + overallAction;
		//System.out.println("its overall: " + newOverall/1000000000);
	}	
	protected static void control() {
		while(!EHCScanner.hasNextInt()) {
			System.out.println("needs to be an int .. ");
			EHCScanner.nextLine();
		}	
	}
	protected static void controlWhile() {
		if(!EHCScanner.equals("quit")) {
			System.out.println("Type: " + "quit" + "to exit ");
			EHCScanner.nextLine();
		}
		else if(EHCScanner.equals("quit")) {
			BestFirstSearch.megaWhileBFS = false;
			EnforcedHillClimbingSearch.validCMD = true;
			EnforcedHillClimbingSearch.controlCMD();
		}
		
	}
	


}

