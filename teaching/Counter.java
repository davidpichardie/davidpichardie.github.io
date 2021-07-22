public class Counter {

    /*
     On se donne une classe `Counter`
     munie de deux méthodes:
     
        int get();
     
     et
     
        void step();
     
     Une instance de cette classe représente une suite d’entiers et une
     position courante dans cette liste.
     La méthode `get` renvoie le terme à la position courante dans cette suite,
     la méthode `step` déplace la position courante vers l'élément suivant dans 
     la suite.
     
     1. [2pt]
        Définir une classe `Nat` qui spécialise la classe `Counter` et qui
        représente la suite des entiers naturels (à partir de zéro).
     
     2. [2pt]
        Définir une classe `Skip` qui spécialise la classe `Counter` et
        est munie d’un constructeur `Skip(Counter base, int step)` qui construit
	la suite extraite de `base` en prenant un terme tous les `step`, et 
	le même terme initial que la suite `base`.
        Par exemple, `new Skip(new Nat(), 2)` construit la suite des entiers
	pairs.
     
     3. [2pt]
        Définir une classe `Difference` qui spécialise la classe `Counter`
        et est munie d’un constructeur `Difference(Counter p, Counter n)`
        qui construit la suite extraite de `p` en ne conservant que les
        termes qui n’apparaissent pas dans `n`.
        On supposera que les suites `p` et `n` sont strictement croissantes et
	different sur au moins un terme.
     
     4. [2pt]
        Définir une classe `Eratosthenes` qui spécialise la classe `Counter`
        et représente la suite des nombres premiers.
        On s’appuiera uniquement sur les classes définies précédemment :
        à partir de la suite des entiers (plus grands que deux),
        dès que l’on a trouvé un nombre premier, on retire de la suite tous 
	ses multiples.
    */
    
	public Counter() {}

	int get() { throw new RuntimeException("Pas implement� ici"); }

	void step() { throw new RuntimeException("Pas implement� ici"); }	

	static void test(String msg, boolean test) {
		if (test) System.out.println(msg+" : succ�s"); 
		else System.out.println(msg+" : �chec");
	}

	public static void main(String[] args) {
	/* Enlever ce commentaire pour tester la classe Nat
		Counter nat = new Nat();
		test ("nat[0]==0", nat.get()==0);
		nat.step();
		test ("nat[1]==1", nat.get()==1);
		nat.step();
		test ("nat[2]==2", nat.get()==2);
		nat.step();
		test ("nat[3]==3", nat.get()==3); */

    /* Enlever ce commentaire pour tester la classe Skip
		Counter even = new Skip(new Nat(), 2);
		test ("even[0]==0", even.get()==0);
		even.step();
		test ("even[1]==2", even.get()==2);
		even.step();
		test ("even[2]==4", even.get()==4);
		even.step();
		test ("even[3]==6", even.get()==6); */

    /* Enlever ce commentaire pour tester la classe Difference
		Counter odd = new Difference(new Nat(), new Skip (new Nat(), 2));
		test ("odd[0]==1", odd.get()==1);
		odd.step();
		test ("odd[1]==3", odd.get()==3);
		odd.step();
		test ("odd[2]==5", odd.get()==5);
		odd.step();
		test ("odd[3]==7", odd.get()==7); */

    /* Enlever ce commentaire pour tester la classe Eratosthenes
		Counter prime = new Eratosthenes();
		test ("prime[0]==2", prime.get()==2);
		prime.step();
		test ("prime[1]==3", prime.get()==3);
		prime.step();
		test ("prime[2]==5", prime.get()==5);
		prime.step();
		test ("prime[3]==7", prime.get()==7);
		prime.step();
		test ("prime[4]==11", prime.get()==11);
		prime.step();
		test ("prime[5]==13", prime.get()==13);
		prime.step();
		test ("prime[6]==17", prime.get()==17);
		prime.step();
		test ("prime[7]==19", prime.get()==19);
		prime.step();
		test ("prime[8]==23", prime.get()==23);
		prime.step();
		test ("prime[9]==29", prime.get()==29); */
	}

}

class Nat extends Counter {
    private int counter;

    public Nat() {
	throw new RuntimeException("TODO");
    }

    @Override int get() { 
	throw new RuntimeException("TODO");
    }

    @Override void step() { 
	throw new RuntimeException("TODO");
    }       
    
}

class Skip extends Counter {

	public Skip(Counter seq, int step) {
		throw new RuntimeException("TODO");
	}

	@Override int get() {
		throw new RuntimeException("TODO");
	}

	@Override void step() { 
		throw new RuntimeException("TODO");
	}
}

class Difference extends Counter {

	public Difference(Counter p, Counter n) {
		throw new RuntimeException("TODO");
	}

	@Override int get() { 
		throw new RuntimeException("TODO");
	}

	@Override void step() { 
		throw new RuntimeException("TODO");
	}
}

class Eratosthenes extends Counter {

	public Eratosthenes() {
		throw new RuntimeException("TODO");
	}

	@Override int get() { 
		throw new RuntimeException("TODO");
	}

	@Override void step() {
		throw new RuntimeException("TODO");
	}
}
