import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class TheoremProver {
	public static void main(String[] args) throws FileNotFoundException {
		printResults = new ArrayList<>();
		
		File testCase = new File(FILE_PATH);
		clauses = ClauseParser.parse(testCase);
		
		System.out.println("Number of clauses: " + clauses.size());
		for (int i = 0; i < clauses.size(); i++) printClause(clauses.get(i));
		System.out.println();
		
		if (IS_UNIT_PREFERENCE) {
			List<Clause> former = new ArrayList<Clause>(clauses.subList(0, GOAL_CLAUSE_START_INDEX));
			List<Clause> latter = new ArrayList<Clause>(clauses.subList(GOAL_CLAUSE_START_INDEX, clauses.size()));
			Collections.sort(former, new Comparator<Clause>() {
				public int compare(Clause c1, Clause c2) {
					return ((c1.getPosSize() + c1.getNegSize()) - (c2.getPosSize() + c2.getNegSize()));
				}
			});
			
			clauses.clear();
			clauses.addAll(former);
			clauses.addAll(latter);
		}
		
		System.out.println("Resolution starts here:");
		
		resolutionStepCount = 0;
		
		int clauseNumber = 1;
		for (clauseNumber = 1; clauseNumber <= clauses.size(); clauseNumber++) {
			StringBuilder sb = new StringBuilder();
			sb.append("(" + clauseNumber + ") ");
			sb.append(clauses.get(clauseNumber - 1).toString());
			printResults.add(sb.toString());
		}
		
		int i = 0;
		int j = GOAL_CLAUSE_START_INDEX;
		while (true) {
			if (j >= clauses.size()) {
				System.out.println("Cannot be proved.");
				break;
			}
			
			if (i >= j) {
				i = 0;
				j++;
				continue;
			}
			
			Clause ci = clauses.get(i);
			Clause cj = clauses.get(j);
			
			System.out.println("The " + i + "th clause: ");
			printClause(ci);
			System.out.println("The " + j + "th clause: ");
			printClause(cj);
			
			Clause resoResult = resolution(ci, cj);
			System.out.println("Resolution result");
			printClause(resoResult);
			
			resolutionStepCount++;
			
			if (resoResult.getPosLits().size() == 0 && resoResult.getNegLits().size() == 0) {
				System.out.println("Proved from clauses: " + i + ", " + j);
				System.out.println("Proved in " + resolutionStepCount + " steps");
				
				for (String toPrint : printResults) System.out.println(toPrint);
				
				break;
			}
			
			if ((!hasRepeat(resoResult)) 
			 && (resoResult.getPosSize() + resoResult.getNegSize() < (IS_UNIT_PREFERENCE ? Math.max(ci.getPosSize() + ci.getNegSize(), cj.getPosSize() + cj.getNegSize()) : ci.getPosSize() + ci.getNegSize() + cj.getPosSize() + cj.getNegSize())))
			{
				clauses.add(resoResult);
				clauseNumber++;
				StringBuilder sb = new StringBuilder();
				sb.append("(" + (clauseNumber - 1) + ") ");
				sb.append(resoResult.toString());
				sb.append(" Parents: " + i + ", " + j);
				printResults.add(sb.toString());
				
				System.out.println("New clause added:");
				printClause(resoResult);
				System.out.println("Resolved from " + i + " and " + j);
			}
			
			i++;
		}
	}

	public static void printClause(Clause c) {
		System.out.println("Clause");
		
		System.out.println("Positive literals: ");
		for (Literal lit : c.getPosLits()) {
			System.out.println("Function name: " + lit.funcName);
			System.out.print("Arguments: ");
			for (String arg : lit.arguments) System.out.print(arg + ", ");
			System.out.println();
		}
		
		System.out.println("Negative literals: ");
		for (Literal lit : c.getNegLits()) {
			System.out.println("Function name: " + lit.funcName);
			System.out.print("Arguments: ");
			for (String arg : lit.arguments) System.out.print(arg + ",");
			System.out.println();
		}
		
		System.out.println("");
	}
	
	private static Clause resolution(Clause c1, Clause c2) {
		List<Literal> posLits = new ArrayList<>();
		List<Literal> negLits = new ArrayList<>();
		
		Set<Integer> mergedPosIndices1 = new HashSet<>();
		Set<Integer> mergedNegIndices1 = new HashSet<>();
		Set<Integer> mergedPosIndices2 = new HashSet<>();
		Set<Integer> mergedNegIndices2 = new HashSet<>();
		
		for (int i = 0; i < c1.getPosSize(); i++) {
			if (mergedPosIndices1.contains(i)) continue;
			
			Literal l1 = c1.getPosLits().get(i);
			
			for (int j = 0; j < c2.getNegSize(); j++) {
				if (mergedNegIndices2.contains(j)) continue;
				
				Literal l2 = c2.getNegLits().get(j);
				
				if (!l1.funcName.equals(l2.funcName)) continue;
				if (Literal.isSame(l1.arguments, l2.arguments)) {
					mergedPosIndices1.add(i);
					mergedNegIndices2.add(j);
					break;
				} else {
					System.out.println("Unify");
					
					for (int argIdx = 0; argIdx < l1.arguments.size(); argIdx++) {
						String arg1 = l1.arguments.get(argIdx);
						String arg2 = l2.arguments.get(argIdx);
						
						if (!arg1.equals(arg2)) {
							if (!Character.isLowerCase(arg1.charAt(0)) && !Character.isLowerCase(arg2.charAt(0))) continue;
							if (Character.isLowerCase(arg1.charAt(0)) && !Character.isLowerCase(arg2.charAt(0))) return(resolution(Clause.unify(c1, arg1, arg2), c2));
							if (Character.isLowerCase(arg2.charAt(0)) && !Character.isLowerCase(arg1.charAt(0))) return(resolution(Clause.unify(c2, arg2, arg1), c1));
							return Clause.unify(c1, arg1, arg2);
						}
					}
				}
			}
		}
		
		for (int i = 0; i < c1.getNegSize(); i++) {
			if (mergedNegIndices1.contains(i)) continue;
			
			Literal l1 = c1.getNegLits().get(i);
			
			for (int j = 0; j < c2.getPosSize(); j++) {
				if (mergedPosIndices2.contains(j)) continue;
				
				Literal l2 = c2.getPosLits().get(j);
				
				if (!l1.funcName.equals(l2.funcName)) continue;
				if (Literal.isSame(l1.arguments, l2.arguments)) {
					mergedNegIndices1.add(i);
					mergedPosIndices2.add(j);
					break;
				} else {
					System.out.println("Unify");
					
					for (int argIdx = 0; argIdx < l1.arguments.size(); argIdx++) {
						String arg1 = l1.arguments.get(argIdx);
						String arg2 = l2.arguments.get(argIdx);
						
						if (!arg1.equals(arg2)) {
							if (!Character.isLowerCase(arg1.charAt(0)) && !Character.isLowerCase(arg2.charAt(0))) continue;
							if (Character.isLowerCase(arg1.charAt(0)) && !Character.isLowerCase(arg2.charAt(0))) return(resolution(Clause.unify(c1, arg1, arg2), c2));
							if (Character.isLowerCase(arg2.charAt(0)) && !Character.isLowerCase(arg1.charAt(0))) return(resolution(Clause.unify(c2, arg2, arg1), c1));
							return Clause.unify(c1, arg1, arg2);
						}
					}
				}
			}
		}
		
		for (int i = 0; i < c1.getPosSize(); i++) {
			if (mergedPosIndices1.contains(i)) continue;
			posLits.add(c1.getPosLits().get(i));
		}
		
		for (int i = 0; i < c1.getNegSize(); i++) {
			if (mergedNegIndices1.contains(i)) continue;
			negLits.add(c1.getNegLits().get(i));
		}
		
		for (int i = 0; i < c2.getPosSize(); i++) {
			if (mergedPosIndices2.contains(i)) continue;
			posLits.add(c2.getPosLits().get(i));
		}
		
		for (int i = 0; i < c2.getNegSize(); i++) {
			if (mergedNegIndices2.contains(i)) continue;
			negLits.add(c2.getNegLits().get(i));
		}
		
		return new Clause(posLits, negLits);
	}
	
	private static boolean hasRepeat(Clause c) {
		for (Clause c1 : clauses)
			if (!Clause.isSame(c, c1)) return false;
		
		return true;
	}
	
	private static List<Clause> clauses;
	private static List<String> printResults;
	private static int resolutionStepCount;
	
	private static final String FILE_PATH = "/Users/tianshuchu/Documents/Study/ArtificialIntelligence/Program/prog2/TheoremProver/src/theorems4";
	private static final int GOAL_CLAUSE_START_INDEX = 6;
	private static final boolean IS_UNIT_PREFERENCE = true;
}
