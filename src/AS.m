
load "src/sqisign.m";

// hard problem KeyGen / all KeyGen
// generates: [y, (E_Y, P_Y, Q_Y, pi_Y)]

// presign: (tau, message, E_Y) --> (presig, tau(P_Y), tau(Q_Y))
// start with sqisign
// extend commitment to depend on E_Y
// compute tau(P_Y), tau(Q_Y)
sqisign := function(sk,pk,K,phi_K,isom_K,J,phi_J,epsilon)
	order:=O0;
	B<i,j,k>:=Parent(Basis(order)[1]);
	w1 := i;
	w2 := j;
	// signing_odd_torsion:=3^53*5^21; //should not be bigger than p/N
	signing_odd_torsion:=1;

	message := [Random(1,2^32-1),Random(1,2^64-1) ];
		//generate  challenge + commitment
		t:=ClockCycles();
		commitment,phi_commit,phi_commit_dual,I_commit:=gen_commitment_odd();
		commit_time:=timediff(t);
		tt:=ClockCycles();
		phi_chall,chall,H_chall:=gen_honest_challenge_prover(phi_commit_dual,I_commit,message);
		challenge_time :=timediff(tt);

		//generate the signature ideal
		tt:=ClockCycles();
		equivalent_ideal:=small_equivalent_ideal(Conjugate(sk)*H_chall);
		_,alpha:=LeftIsomorphism(J,sk);
		sign_ideal:=QuaternionIsogenyPath_special_Extended2(order,w1,w2,equivalent_ideal,sk,2:addit_factor:=signing_odd_torsion);
		sign_ideal:=cyclic_ideal(sign_ideal:full:=true);
		klpt_time:=timediff(tt);
		sign_ideal:=sign_ideal*lideal<RightOrder(sign_ideal)|Conjugate(alpha)/Norm(alpha)>;
		sign_ideal:=rideal<LeftOrder(sign_ideal)|alpha>*sign_ideal;

		//computing the signature isogeny
		tt:=ClockCycles();
		sign_isogeny,sign_isom,_:=ideal_to_isogeny_power_of_two(sign_ideal,J,K,phi_J,phi_K,isom_K,epsilon:other_side_isogeny:=phi_commit cat phi_chall,other_side_ideal:=H_chall);
		 // sign_isogeny,sign_isom,_:=ideal_to_isogeny_power_of_two(J*sign_ideal,J,K,phi_J,phi_K,isom_K,epsilon);
		 translate_time:=timediff(tt);
		//normalizing and compressing
		walk, zip, last_step,len:=normalized_two_walk(sign_isogeny,sign_isom);
		sign_time:=timediff(t);


		//computing the verification
		tt:=ClockCycles();
		ver:=verify(commitment,message,zip,pk,len,last_step);
		assert(ver);
		if not ver then "problem with the verification"; end if;
		verif_time:=timediff(tt);

	return commit_time,challenge_time,klpt_time,translate_time,sign_time,verif_time,Valuation(Z!Norm(sign_ideal),2);
end function;


// adapt: (presig, y) --> (sig, pi_y')
// run sidh to get E_yA
// compose isogenies and run KLPT

// extract: (presig, sig) --> (y)

// verify

end procedure;
