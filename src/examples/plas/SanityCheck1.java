package plas;


/*
 * Toy program from paper of Newsome et. al: "Measuring channel capacity to
 * distinguish undue influence"
 */

public class SanityCheck1 {
	
	public int func(int H, int L){
		int O;
		if (H < 16)
			O = L + H;
		else
			O = L;
		return O;		
	}
	
	public static void main(String[] args) {
		SanityCheck1 o = new SanityCheck1();
		o.func(1,0x00001000);
	}
}