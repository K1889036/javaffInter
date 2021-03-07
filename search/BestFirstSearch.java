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

import javaff.planning.State;
import javaff.data.Action;
import javaff.data.Fact;
import javaff.planning.Filter;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashMap;
import java.util.TreeSet;
import java.util.Hashtable;
import java.util.Scanner;
import java.util.List;
import java.util.Set;
import java.util.HashSet;
import java.util.Iterator;
import javaff.JavaFF;

public class BestFirstSearch extends Search
{

	protected Hashtable closed;
	protected TreeSet open;
	protected static boolean searchStartBFS;
	protected static boolean searchBFS;
	protected static boolean actionPhaseBFS;
	protected static boolean megaWhileBFS;
	protected static State stateBFS;
	private boolean legal;
	protected static boolean test;
	public static long startActionBFS;
	public static long endActionBFS;
	public static long overallBFS;
	public static long newOverallBFS;
	
	public BestFirstSearch(State s)
	{
		this(s, new HValueComparator());
	}
	
	public BestFirstSearch(State s, Comparator c)
	{
		super(s);
		setComparator(c);

		closed = new Hashtable();
		open = new TreeSet(comp);
	}

	public void updateOpen(State S)
	{
		open.addAll(S.getNextStates(filter.getActions(S)));
	}

	public State removeNext()
	{
		State S = (State) (open).first();
		open.remove(S);
		/*
		 * System.out.println("================================");
		 * S.getSolution().print(System.out); System.out.println("----Helpful
		 * Actions-------------"); javaff.planning.TemporalMetricState ms =
		 * (javaff.planning.TemporalMetricState) S;
		 * System.out.println(ms.helpfulActions);
		 * System.out.println("----Relaxed Plan----------------");
		 * ms.RelaxedPlan.print(System.out);
		 */
		return S;
	}
	
	public boolean needToVisit(State s)
	{
		Integer Shash = new Integer(s.hashCode());
		State D = (State) closed.get(Shash);

		if (closed.containsKey(Shash) && D.equals(s))
			return false;

		closed.put(Shash, s);
		return true;
	}
	/*public void megaWhile() {
		System.out.println("Here you can view all the non applicable actions for the current state"+"\n"
				+ "Type: -show- to view the different actions. "+"\n"
				+ "Type: -quit- to go back to the main interface.."
				);
		String whileCMD = EnforcedHillClimbingSearch.EHCScanner.nextLine();
		
		if(megaWhileBFS==true && (whileCMD.equals("show"))) {
				getNonAppli(stateBFS);
		}
		else if(whileCMD.equals("quit") && megaWhileBFS==true) {
			megaWhileBFS = false;
			EnforcedHillClimbingSearch.validCMD = true;
		}
		
	}*/
	public void megaWhile() {
		
	}
	public void getNonAppli(State s) {
		
		System.out.println("Here you can view all the non applicable actions for the current state"+"\n");
		int nANum=0;
		int ctrl=0;

		while(megaWhileBFS == true || ctrl!=0) {
		System.out.println("How many action do you want to display? There is a total of "+filter.getNonApplicableActions(s).size()+ " non applicable actions.. \n"
				+ "To exit this menu input: 0");
		
			EnforcedHillClimbingSearch.control();
			ctrl = EnforcedHillClimbingSearch.EHCScanner.nextInt();
			System.out.println("this is ctrl: "+ctrl);
			if(ctrl==0) {
				megaWhileBFS=false;
			}
			else if(ctrl>filter.getNonApplicableActions(s).size() || ctrl<=-1) {
				System.out.println("it is an invalid number");
				//ctrl = EnforcedHillClimbingSearch.EHCScanner.nextInt();
			}
			else if(ctrl <=filter.getNonApplicableActions(s).size()){
				HashMap<Integer,Action> nonApplicableAction = new HashMap<Integer,Action>();
				for(int i =0; i < ctrl; i++) {
					nANum++;
					Action actionsNonApplicable = filter.getNonApplicableActions(s).get(i);
					nonApplicableAction.put(nANum, actionsNonApplicable);
					System.out.println(nANum +" "+ actionsNonApplicable); 	// want to print this
				}
				EnforcedHillClimbingSearch.control();
				int nonActionSelectorBFS = EnforcedHillClimbingSearch.EHCScanner.nextInt();
				if(nonActionSelectorBFS <= nANum && nonActionSelectorBFS >= 1){
					EnforcedHillClimbingSearch.EHCScanner.nextLine();
					Action actionSelected = nonApplicableAction.get(nonActionSelectorBFS);

					if(actionSelected.getPreconditions().size() > 1) {
						System.out.println("In order to apply this action, you must meet these "+actionSelected.getPreconditions().size()+ " requirements: " +actionSelected.getPreconditions());
					}
					else if((actionSelected.getPreconditions().size() <= 1)){
						System.out.println("In order to apply this action, you must meet this "+actionSelected.getPreconditions().size()+ " requirement: " +actionSelected.getPreconditions());
					}
					System.out.println("Your current state is: "+stateBFS);
					System.out.println("You are missing one or more of the precondition..."); //TODO better this
				}
				megaWhileBFS = false;
				ctrl = 0;
			}
		}

	}
	public <T> List<T> intersection(List<State>list1, List<Fact>list2){
		List<T>list = new ArrayList<T>();
		for(State t : list1) {
			if(list2.contains(t)) {
				//list.add(t);
			}
		}
		return list;
	}

	public State search()
	{
		searchStartBFS = true;
		searchBFS = true;
		startActionBFS = System.nanoTime();
		EnforcedHillClimbingSearch.controlCMD();
		endActionBFS = System.nanoTime();
		overallBFS = endActionBFS - startActionBFS;
		newOverallBFS = newOverallBFS + overallBFS;
		System.out.println("Around here overall fs = "+newOverallBFS/1000000000);
		//Scanner BFSScanner = new Scanner(System.in);
		System.out.println("Select limit of nodes to expend using Best First Search. ");
		//if(EnforcedHillClimbingSearch.EHCScanner.hasNextInt()) {
		//EnforcedHillClimbingSearch.control();
			//int z = EnforcedHillClimbingSearch.EHCScanner.nextInt();
			
// implement the scanner here. for nodeCount.
		
			open.add(start);
			System.out.println("qqweqweq "+start);
			while (!open.isEmpty())
			{
				State s = removeNext();
				//System.out.println("print "+s);
				stateBFS = s;
				//filter.getNonApplicableActions(s);
				if (needToVisit(s))
				{
					++nodeCount; 
					++nodeCountAct;
					System.out.println(nodeCount); 
					//System.out.println(s); //prints current state.
					//System.out.println(filter.getActions(s)); 
					if (s.goalReached())
					{
						return s;
					} 
					else if(nodeCountAct >= EnforcedHillClimbingSearch.z) {
						actionPhaseBFS = true;
						test = true;
						//megaWhileBFS = false;
						//System.out.println("iki "+getNonAppli(s));
						startActionBFS = System.nanoTime();
						while(test=true) {
							EnforcedHillClimbingSearch.controlCMD();
							if(megaWhileBFS == true) {	
								getNonAppli(stateBFS);
							}
							else if(test==false) {
								break;
							}
							else{
								EnforcedHillClimbingSearch.controlCMD();
							}
						}
						//need to figure out how to implement the non applicable actions.
						
						int num = 0;
						HashMap<Integer,Action> ActionMapBFS = new HashMap<Integer,Action>();
						System.out.println("select an action to apply: ");
						for(int i =0; i < filter.getActions(s).size(); i++) {
							num++;
							ActionMapBFS.put(num, filter.getActions(s).get(i));
							System.out.println(num +" "+ filter.getActions(s).get(i)); // want to print this
						}

						boolean valid = true;
						while(valid) {
							while(!EnforcedHillClimbingSearch.EHCScanner.hasNextInt()) {
								EnforcedHillClimbingSearch.EHCScanner.nextLine();
								System.out.println("The input needs to be an integer...");
							}
							int actionSelectorBFS = EnforcedHillClimbingSearch.EHCScanner.nextInt();
								if(actionSelectorBFS <= num && actionSelectorBFS >= 1){
									EnforcedHillClimbingSearch.EHCScanner.nextLine();
									System.out.println("You have applied: "+ActionMapBFS.get(actionSelectorBFS));
									nodeCountAct = 0;
									s = s.getNextState(ActionMapBFS.get(actionSelectorBFS));
									open.clear(); // might be wrong to do like this.
									//System.out.println(open);
									open.add(s);
									//System.out.println(open);
									updateOpen(s);
									valid = false;
								} else {
									System.out.println("Please input a valid action...");
									EnforcedHillClimbingSearch.EHCScanner.nextLine();
								}
							
						}
						endActionBFS = System.nanoTime();
						overallBFS = endActionBFS - startActionBFS;
						newOverallBFS = newOverallBFS + overallBFS;
						System.out.println("BFS OVERALL HERE IS; "+ newOverallBFS/1000000000);
						//System.out.println("You have applied: "+ActionMapBFS.get(actionSelectorBFS));
						//nodeCountAct = 0;
						//s = s.getNextState(ActionMapBFS.get(actionSelectorBFS));// need to  figure out how to apply an action here. This does not work correctly..
						//System.out.println(open);
						
						//System.out.println(open);
						
						//updateOpen(s);

			//			System.out.println(s + "testing");
					} 
					
					else
					{
						//System.out.println(open);
						updateOpen(s);

					//	System.out.println(s + "idkkkkk");
					//	System.out.println(open);
					}
				}
			}
			
		
		return null;
	}

}
