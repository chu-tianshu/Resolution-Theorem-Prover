import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.List;
import java.util.Scanner;

public class ClauseParser {
	public static List<Clause> parse(File testCase) throws FileNotFoundException {
		List<Clause> result = new ArrayList<>();
		
		List<String> clauseStrings = ClauseParser.toStringArray(testCase);
		for (String s : clauseStrings) result.add(ClauseParser.parseClause(s));
		
		return result;
	}
	
	public static List<String> toStringArray(File testCase) throws FileNotFoundException {
		List<String> result = new ArrayList<>();
		
		Scanner sc = new Scanner(testCase);
		while (sc.hasNextLine()) result.add(sc.nextLine());
		
		return result;
	}
	
	public static Clause parseClause(String s) {
		int posStart = 0;
		int posEnd = 1;
		int negEnd = s.length() - 1;
		int negStart = s.length() - 2;
		
		int leftCount = 1;
		for (int i = 1; i < s.length(); i++) {
			if (s.charAt(i) == '(') leftCount++;
			if (s.charAt(i) == ')') {
				if (leftCount == 1) {
					posEnd = i;
					break;
				}
				
				leftCount--;
			}
		}
		
		int rightCount = 1;
		for (int i = s.length() - 2; i >= 0; i--) {
			if (s.charAt(i) == ')') rightCount++;
			if (s.charAt(i) == '(') {
				if (rightCount == 1) {
					negStart = i;
					break;
				}
				
				rightCount--;
			}
		}
		
		List<Literal> posLiterals = new ArrayList<>();
		List<Literal> negLiterals = new ArrayList<>();
		
		int posLeft = posStart + 1;
		while (true) {
			while (posLeft < posEnd && s.charAt(posLeft) != '(') posLeft++;
			if (posLeft >= posEnd) break;
			
			int posRight = posLeft + 1;
			while (s.charAt(posRight) != ')') posRight++;
			
			posLiterals.add(parseLiteral(s.substring(posLeft + 1, posRight)));
			
			posLeft = posRight + 1;
		}
		
		int negLeft = negStart + 1;
		while (true) {
			while (negLeft < negEnd && s.charAt(negLeft) != '(') negLeft++;
			if (negLeft >= negEnd) break;
			
			int negRight = negLeft + 1;
			while (s.charAt(negRight) != ')') negRight++;
			
			negLiterals.add(parseLiteral(s.substring(negLeft + 1, negRight)));
			
			negLeft = negRight + 1;
		}
		
		return new Clause(posLiterals, negLiterals);
	}

	private static Literal parseLiteral(String s) {
		return new Literal(s.split(" "));
	}
}
