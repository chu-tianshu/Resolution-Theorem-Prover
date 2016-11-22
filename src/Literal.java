import java.util.ArrayList;
import java.util.List;

public class Literal {
	public Literal() {
		this.funcName = new String();
		this.arguments = new ArrayList<>();
	}
	
	public Literal(String[] arr) {
		this.funcName = arr[0];
		this.arguments = new ArrayList<>();
		for (int i = 1; i < arr.length; i++) this.arguments.add(arr[i]);
	}
	
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append(funcName);
		sb.append("(");
		for (String arg : arguments) sb.append(arg + " ");
		sb.deleteCharAt(sb.length() - 1);
		sb.append(")");
		return sb.toString();
	}
	
	public static boolean isSame(List<String> args1, List<String> args2) {
		if (args1.size() != args2.size()) return false;

		for (int i = 0; i < args1.size(); i++)
			if (!args1.get(i).equals(args2.get(i))) return false;
		
		return true;
	}
	
	public String funcName;
	public List<String> arguments;
}