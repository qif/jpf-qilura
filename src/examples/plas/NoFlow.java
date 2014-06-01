package plas;

public class NoFlow {
	
	public int func(int H){
		int O;
		if ( H > 999 ) 
			O = -1;
		O = H;
		O = O - H;
		return O;
	}
	
	public static void main(String[] args) {
		NoFlow o = new NoFlow();
		o.func(1);
	}
}
