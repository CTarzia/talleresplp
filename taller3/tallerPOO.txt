// Definiciones globales (no modificar acá, en cambio, completar las funciones ejercicio_i)
let qf;
let q1;
let q2;
let q3;
let Estado;
let algunoAcepta;
let esDeterministico;
let esDeterministicoOVisitado;

// Ejercicio 1
function ejercicio1() {
	qf = {
		esFinal: true,
		transiciones: {},
		acepta: (s) => s === "",
	};
	q3 = {
		esFinal: true,
		transiciones: {},
	};
	q2 = {
		esFinal: true,
		transiciones: { c: q3 },
	};
	q1 = {
		esFinal: false,
		transiciones: { b: q2, c: q3 },
	};
	q1.transiciones.a = q1;
}

// Ejercicio 2
function ejercicio2() {
	String.prototype.head = function () {
		return this[0];
	};
	String.prototype.tail = function () {
		return this.slice(1);
	};
}

// Ejercicio 3
function ejercicio3() {
	Estado = function (esFinal, transiciones) {
		this.esFinal = esFinal;
		this.transiciones = transiciones;
		this.acepta = function (cadena) {
			if (cadena === "") return this.esFinal;
			const estadoNuevo = this.transiciones[cadena.head()];
			if (!estadoNuevo) return false;
			return estadoNuevo.acepta(cadena.tail());
		};
	};

	const proto = new Estado(null, null);
	[q1, q2, q3].forEach(e => Object.setPrototypeOf(e, proto));
}

// Ejercicio 4
function ejercicio4() {
	Estado.prototype.nuevaTransicion = function (etiqueta, destino) {
		this.transiciones = Object.assign({}, this.transiciones);
		this.transiciones[etiqueta] = destino;
	};
}

// Ejercicio 5
function ejercicio5() {
	algunoAcepta = function (s, qs) {
		if (Array.isArray(qs)) {
			return qs.some((q) => q.acepta(s));
		}
		return qs.acepta(s);
	};
}

// Ejercicio 6
function ejercicio6() {
	Estado.prototype.nuevaTransicionND = function (etiqueta, destino) {
		this.transiciones = Object.assign({}, this.transiciones);
		const destinoEtiqueta = this.transiciones[etiqueta];
		if (!destinoEtiqueta) {
			this.transiciones[etiqueta] = destino;
		} else {
			if (Array.isArray(destinoEtiqueta)) {
				if (!destinoEtiqueta.includes(destino))
					this.transiciones[etiqueta] = [...destinoEtiqueta, destino];
			} else {
				if (destinoEtiqueta != destino) {
					this.transiciones[etiqueta] = [destinoEtiqueta, destino];
					this.acepta = function (cadena) {
						if (cadena == "") return this.esFinal;
						const estadoNuevo = this.transiciones[cadena.head()];
						if (!estadoNuevo) return false;
						return algunoAcepta(cadena.tail(), estadoNuevo);
					};
				}
			}
		}
	};
}

// Ejercicio 7
function ejercicio7() {
	esDeterministicoOVisitado = function (q, estadosVisitados) {
		for (etiqueta in q.transiciones) {
			if (!estadosVisitados.includes(etiqueta)) {
				if (!Array.isArray(q.transiciones[etiqueta])) {
					estadosVisitados.push(etiqueta);
					esDeterministicoOVisitado(q.transiciones[etiqueta], estadosVisitados);
				} else return false;
			}
		}
		return true;
	};

	esDeterministico = function (q) {
		const estadosVisitados = [];
		let res = true;
		for (etiqueta in q.transiciones) {
			if (!Array.isArray(q.transiciones[etiqueta]) || !res) {
				estadosVisitados.push(etiqueta);
				res = res && esDeterministicoOVisitado(q.transiciones[etiqueta], estadosVisitados);
			} else return false;
		}
		return res;
	};
}

// Test Ejercicio 1
function testEjercicio1(res) {
	let qf_es_final = qf.esFinal;
	let qf_tiene_transiciones = qf.transiciones != undefined;
	let qf_tiene_transiciones_no_vacias =
		Object.getOwnPropertyNames(qf.transiciones).length > 0;
	let qf_acepta_vacio = qf.acepta("");
	let qf_acepta_paradigmas = qf.acepta("paradigmas");

	res.write("qf" + si_o_no(qf_es_final) + "es un estado final", qf_es_final);
	res.write(
		"qf" +
			si_o_no(qf_tiene_transiciones) +
			'sabe responder al mensaje "transiciones"',
		qf_tiene_transiciones
	);
	res.write(
		"qf" +
			si_o_no(qf_tiene_transiciones_no_vacias) +
			"tiene transiciones hacia otros estados",
		!qf_tiene_transiciones_no_vacias
	);
	res.write(
		"qf" + si_o_no(qf_acepta_vacio) + "acepta la cadena vacía",
		qf_acepta_vacio
	);
	res.write(
		"qf" + si_o_no(qf_acepta_paradigmas) + 'acepta la cadena "paradigmas"',
		!qf_acepta_paradigmas
	);

	res.write("----------------------------------------------------------------");

	let q1_es_final = q1.esFinal;
	let q2_es_final = q2.esFinal;
	let q3_es_final = q3.esFinal;

	res.write("q1" + si_o_no(q1_es_final) + "es un estado final", !q1_es_final);
	res.write("q2" + si_o_no(q2_es_final) + "es un estado final", q2_es_final);
	res.write("q3" + si_o_no(q3_es_final) + "es un estado final", q3_es_final);

	let q1_a_q1 = q1.transiciones["a"] == q1;
	let q1_b_q2 = q1.transiciones["b"] == q2;
	let q1_c_q3 = q1.transiciones["c"] == q3;
	let q2_c_q3 = q2.transiciones["c"] == q3;

	res.write(
		"q1" + si_o_no(q1_a_q1) + 'transiciona a q1 mediante la etiqueta "a"',
		q1_a_q1
	);
	res.write(
		"q1" + si_o_no(q1_b_q2) + 'transiciona a q2 mediante la etiqueta "b"',
		q1_b_q2
	);
	res.write(
		"q1" + si_o_no(q1_c_q3) + 'transiciona a q3 mediante la etiqueta "c"',
		q1_c_q3
	);
	res.write(
		"q2" + si_o_no(q2_c_q3) + 'transiciona a q3 mediante la etiqueta "c"',
		q2_c_q3
	);

	let q1_tiene_demasiadas_transiciones =
		Object.getOwnPropertyNames(q1.transiciones).length > 3;
	let q2_tiene_demasiadas_transiciones =
		Object.getOwnPropertyNames(q2.transiciones).length > 1;
	let q3_tiene_transiciones =
		Object.getOwnPropertyNames(q3.transiciones).length > 0;

	res.write(
		"q1" +
			si_o_no(q1_tiene_demasiadas_transiciones) +
			"tiene más de 3 transiciones salientes",
		!q1_tiene_demasiadas_transiciones
	);
	res.write(
		"q2" +
			si_o_no(q2_tiene_demasiadas_transiciones) +
			"tiene más de 1 transición saliente",
		!q2_tiene_demasiadas_transiciones
	);
	res.write(
		"q3" + si_o_no(q3_tiene_transiciones) + "tiene transiciones salientes",
		!q3_tiene_transiciones
	);
}

// Test Ejercicio 2
function testEjercicio2(res) {
	let head_paradigmas = "paradigmas".head();
	let tail_paradigmas = "paradigmas".tail();
	let tail_a_es_vacia = "a".tail() == "";

	res.write(
		'El primer caracter de "paradigmas" es "' + head_paradigmas + '"',
		head_paradigmas == "p"
	);
	res.write(
		'El final de la cadena "paradigmas" es "' + tail_paradigmas + '"',
		tail_paradigmas == "aradigmas"
	);
	res.write(
		'El final de la cadena "a"' +
			si_o_no(tail_a_es_vacia) +
			"es la cadena vacía",
		tail_a_es_vacia
	);
}

// Test Ejercicio 3
function testEjercicio3(res) {
	res.write(
		"Creo un estado qnuevo que no es final y tiene transiciones {x: q1, y: q2, z: q3}\n"
	);

	let qnuevo = new Estado(false, { x: q1, y: q2, z: q3 });
	let qnuevo_definido = qnuevo != undefined;
	let qnuevo_es_final = qnuevo.esFinal;
	let qnuevo_acepta_vacio = qnuevo.acepta("");
	let qnuevo_acepta_xab = qnuevo.acepta("xab");

	res.write(
		"qnuevo" + si_o_no(qnuevo_definido) + "está definido",
		qnuevo_definido
	);
	res.write(
		"qnuevo" + si_o_no(qnuevo_es_final) + "es un estado final",
		!qnuevo_es_final
	);
	res.write(
		"qnuevo" + si_o_no(qnuevo_acepta_vacio) + "acepta la palabra vacía",
		!qnuevo_acepta_vacio
	);
	res.write(
		"qnuevo" + si_o_no(qnuevo_acepta_xab) + 'acepta la palabra "xab"',
		qnuevo_acepta_xab
	);

	res.write("----------------------------------------------------------------");

	let q1_responde_acepta = "acepta" in q1;
	let q2_responde_acepta = "acepta" in q2;
	let q3_responde_acepta = "acepta" in q3;

	res.write(
		"q1" + si_o_no(q1_responde_acepta) + 'sabe responder el mensaje "acepta"',
		q1_responde_acepta
	);
	res.write(
		"q2" + si_o_no(q2_responde_acepta) + 'sabe responder el mensaje "acepta"',
		q2_responde_acepta
	);
	res.write(
		"q3" + si_o_no(q3_responde_acepta) + 'sabe responder el mensaje "acepta"',
		q3_responde_acepta
	);

	let q1_acepta_vacio = q1.acepta("");
	let q1_acepta_a = q1.acepta("a");
	let q1_acepta_ab = q1.acepta("ab");
	let q1_acepta_abc = q1.acepta("abc");
	let q1_acepta_aaaaaaaaac = q1.acepta("aaaaaaaaac");
	let q2_acepta_vacio = q2.acepta("");
	let q2_acepta_c = q2.acepta("c");
	let q3_acepta_vacio = q3.acepta("");
	let q3_acepta_c = q3.acepta("c");

	res.write(
		"q1" + si_o_no(q1_acepta_vacio) + "acepta la palabra vacía",
		!q1_acepta_vacio
	);
	res.write(
		"q1" + si_o_no(q1_acepta_a) + 'acepta la palabra "a"',
		!q1_acepta_a
	);
	res.write(
		"q1" + si_o_no(q1_acepta_ab) + 'acepta la palabra "ab"',
		q1_acepta_ab
	);
	res.write(
		"q1" + si_o_no(q1_acepta_abc) + 'acepta la palabra "abc"',
		q1_acepta_abc
	);
	res.write(
		"q1" + si_o_no(q1_acepta_aaaaaaaaac) + 'acepta la palabra "aaaaaaaaac"',
		q1_acepta_aaaaaaaaac
	);
	res.write(
		"q2" + si_o_no(q2_acepta_vacio) + "acepta la palabra vacía",
		q2_acepta_vacio
	);
	res.write("q2" + si_o_no(q2_acepta_c) + 'acepta la palabra "c"', q2_acepta_c);
	res.write(
		"q3" + si_o_no(q3_acepta_vacio) + "acepta la palabra vacía",
		q3_acepta_vacio
	);
	res.write(
		"q3" + si_o_no(q3_acepta_c) + 'acepta la palabra "c"',
		!q3_acepta_c
	);
}

// Test Ejercicio 4
function testEjercicio4(res) {
	let q1_responde_nuevaTransicion = "nuevaTransicion" in q1;
	let q2_responde_nuevaTransicion = "nuevaTransicion" in q2;
	let q3_responde_nuevaTransicion = "nuevaTransicion" in q3;

	res.write(
		"q1" +
			si_o_no(q1_responde_nuevaTransicion) +
			'sabe responder el mensaje "nuevaTransicion"',
		q1_responde_nuevaTransicion
	);
	res.write(
		"q2" +
			si_o_no(q2_responde_nuevaTransicion) +
			'sabe responder el mensaje "nuevaTransicion"',
		q2_responde_nuevaTransicion
	);
	res.write(
		"q3" +
			si_o_no(q3_responde_nuevaTransicion) +
			'sabe responder el mensaje "nuevaTransicion"',
		q3_responde_nuevaTransicion
	);

	res.write("\nCreo un estado qnuevo, final y sin transiciones\n");

	let qnuevo = new Estado(true, {});
	let qnuevo_tiene_transiciones_definidas =
		Object.getOwnPropertyNames(qnuevo.transiciones).length > 0;

	res.write(
		"qnuevo" +
			si_o_no(qnuevo_tiene_transiciones_definidas) +
			"tiene transiciones definidas",
		!qnuevo_tiene_transiciones_definidas
	);

	res.write('\nAgrego una transición hacia q1 mediante "a"\n');

	qnuevo.nuevaTransicion("a", q1);
	let qnuevo_acepta_ab = qnuevo.acepta("ab");
	let qnuevo_acepta_abc = qnuevo.acepta("abc");

	res.write(
		"qnuevo" + si_o_no(qnuevo_acepta_ab) + 'acepta la palabra "ab"',
		qnuevo_acepta_ab
	);
	res.write(
		"qnuevo" + si_o_no(qnuevo_acepta_abc) + 'acepta la palabra "abc"',
		qnuevo_acepta_abc
	);

	res.write('\nAgrego una transición hacia q2 mediante "a"\n');

	qnuevo.nuevaTransicion("a", q2);
	let qnuevo_acepta_ab_ahora = qnuevo.acepta("ab");
	let qnuevo_acepta_abc_ahora = qnuevo.acepta("abc");
	let qnuevo_acepta_ac = qnuevo.acepta("ac");

	res.write(
		"qnuevo" + si_o_no(qnuevo_acepta_ab_ahora) + 'acepta la palabra "ab"',
		!qnuevo_acepta_ab_ahora
	);
	res.write(
		"qnuevo" + si_o_no(qnuevo_acepta_abc_ahora) + 'acepta la palabra "abc"',
		!qnuevo_acepta_abc_ahora
	);
	res.write(
		"qnuevo" + si_o_no(qnuevo_acepta_ac) + 'acepta la palabra "ac"',
		qnuevo_acepta_ac
	);

	res.write(
		'\nCreo el estado q4, a partir de q1, y le agrego una transición hacia q2 mediante "z"\n'
	);

	let q4 = Object.create(q1);
	q4.nuevaTransicion("z", q2);
	let q4_acepta_z = q4.acepta("z");
	let q1_acepta_z = q1.acepta("z");

	res.write("q4" + si_o_no(q4_acepta_z) + 'acepta la palabra "z"', q4_acepta_z);
	res.write(
		"q1" + si_o_no(q1_acepta_z) + 'acepta la palabra "z"',
		!q1_acepta_z
	);

	res.write(
		'\nCreo el estado q5, con las transiciones de qnuevo, y le agrego una transición hacia q4 mediante "e"\n'
	);

	let q5 = new Estado(false, qnuevo.transiciones);
	q5.nuevaTransicion("e", q4);
	let q5_acepta_ez = q5.acepta("ez");
	let qnuevo_acepta_ez = qnuevo.acepta("ez");
	res.write(
		"q5" + si_o_no(q5_acepta_ez) + 'acepta la palabra "ez"',
		q5_acepta_ez
	);
	res.write(
		"qnuevo" + si_o_no(qnuevo_acepta_ez) + 'acepta la palabra "ez"',
		!qnuevo_acepta_ez
	);
}

// Test Ejercicio 5
function testEjercicio5(res) {
	let q1_acepta_ab = algunoAcepta("ab", q1);
	let q123_aceptan_c = algunoAcepta("c", [q1, q2, q3]);
	let q23_aceptan_b = algunoAcepta("b", [q2, q3]);

	res.write(
		"q1" + si_o_no(q1_acepta_ab) + 'acepta la palabra "ab"',
		q1_acepta_ab
	);
	res.write(
		"q1, q2 o q3" + si_o_no(q123_aceptan_c) + 'aceptan la palabra "c"',
		q123_aceptan_c
	);
	res.write(
		"q2 o q3" + si_o_no(q23_aceptan_b) + 'aceptan la palabra "b"',
		!q23_aceptan_b
	);
}

// Test Ejercicio 6
function testEjercicio6(res) {
	res.write(
		'Creo el estado qnuevo, final y sin transiciones. Le agrego una transición hacia q1 mediante "z"\n'
	);

	qnuevo = new Estado(true, {});
	qnuevo.nuevaTransicionND("z", q1);

	let qnuevo_acepta_zb = qnuevo.acepta("zb");

	res.write(
		"qnuevo" + si_o_no(qnuevo_acepta_zb) + 'acepta la palabra "zb"',
		qnuevo_acepta_zb
	);

	res.write('\nAgrego una transición de qnuevo hacia q2 mediante "x"\n');

	qnuevo.nuevaTransicionND("x", q2);

	let qnuevo_acepta_zb_ahora = qnuevo.acepta("zb");
	let qnuevo_acepta_xc = qnuevo.acepta("xc");

	res.write(
		"qnuevo" + si_o_no(qnuevo_acepta_zb_ahora) + 'acepta la palabra "zb"',
		qnuevo_acepta_zb_ahora
	);
	res.write(
		"qnuevo" + si_o_no(qnuevo_acepta_xc) + 'acepta la palabra "xc"',
		qnuevo_acepta_xc
	);

	res.write('\nAgrego una transición de qnuevo hacia q3 mediante "y"\n');

	qnuevo.nuevaTransicionND("y", q3);

	let qnuevo_acepta_zb_todavia = qnuevo.acepta("zb");
	let qnuevo_acepta_xc_ahora = qnuevo.acepta("xc");
	let qnuevo_acepta_y = qnuevo.acepta("y");

	res.write(
		"qnuevo" + si_o_no(qnuevo_acepta_zb_todavia) + 'acepta la palabra "zb"',
		qnuevo_acepta_zb_todavia
	);
	res.write(
		"qnuevo" + si_o_no(qnuevo_acepta_xc_ahora) + 'acepta la palabra "xc"',
		qnuevo_acepta_xc_ahora
	);
	res.write(
		"qnuevo" + si_o_no(qnuevo_acepta_y) + 'acepta la palabra "y"',
		qnuevo_acepta_y
	);

	res.write('\nAgrego una transición de qnuevo hacia qnuevo mediante "x"\n');

	qnuevo.nuevaTransicionND("x", qnuevo);

	let qnuevo_acepta_xx = qnuevo.acepta("xx");
	qnuevo_acepta_xc = qnuevo.acepta("xc");

	res.write(
		"qnuevo" + si_o_no(qnuevo_acepta_xc) + 'acepta la palabra "xc"',
		qnuevo_acepta_xc
	);
	res.write(
		"qnuevo" + si_o_no(qnuevo_acepta_xx) + 'acepta la palabra "xx"',
		qnuevo_acepta_xx
	);

	res.write(
		'\nCreo el estado q6, a partir de qnuevo, y le agrego una transición hacia q2 mediante "g"\n'
	);

	let q6 = Object.create(qnuevo);
	q6.nuevaTransicionND("g", q2);
	let q6_acepta_gc = q6.acepta("gc");
	let qnuevo_acepta_gc = qnuevo.acepta("gc");

	res.write(
		"q6" + si_o_no(q6_acepta_gc) + 'acepta la palabra "gc"',
		q6_acepta_gc
	);
	res.write(
		"qnuevo" + si_o_no(qnuevo_acepta_gc) + 'acepta la palabra "gc"',
		!qnuevo_acepta_gc
	);

	res.write('\nAgrego una transición de q6 hacia q1 mediante "x"\n');

	q6.nuevaTransicionND("x", q1);
	let q6_acepta_xab = q6.acepta("xab");
	let qnuevo_acepta_xab = qnuevo.acepta("xab");
	q6_acepta_xc = q6.acepta("xc");
	qnuevo_acepta_xc = qnuevo.acepta("xc");

	res.write(
		"q6" + si_o_no(q6_acepta_xc) + 'acepta la palabra "xc"',
		q6_acepta_xc
	);
	res.write(
		"qnuevo" + si_o_no(qnuevo_acepta_xc) + 'acepta la palabra "xc"',
		qnuevo_acepta_xc
	);
	res.write(
		"q6" + si_o_no(q6_acepta_xab) + 'acepta la palabra "xab"',
		q6_acepta_xab
	);
	res.write(
		"qnuevo" + si_o_no(qnuevo_acepta_xab) + 'acepta la palabra "xab"',
		!qnuevo_acepta_xab
	);
}

// Test Ejercicio 7
function testEjercicio7(res) {
	let q1_deterministico = esDeterministico(q1);
	let q2_deterministico = esDeterministico(q2);
	let q3_deterministico = esDeterministico(q3);

	res.write(
		"q1" + si_o_no(q1_deterministico) + "es determinístico",
		q1_deterministico
	);
	res.write(
		"q2" + si_o_no(q2_deterministico) + "es determinístico",
		q2_deterministico
	);
	res.write(
		"q3" + si_o_no(q3_deterministico) + "es determinístico",
		q3_deterministico
	);

	res.write(
		'\nCreo el estado qnuevo, le agrego dos transiciones hacia q1 y q2 mediante "z"'
	);

	qnuevo = new Estado(false, {});
	qnuevo.nuevaTransicionND("z", q1);
	qnuevo.nuevaTransicionND("z", q2);

	let qnuevo_deterministico = esDeterministico(qnuevo);

	res.write(
		"qnuevo" + si_o_no(qnuevo_deterministico) + "es determinístico",
		!qnuevo_deterministico
	);
}

// Función auxiliar que crea un test genérico a partir de un número i y una función f
function crearTest(i, f) {
	return function () {
		if (eval("typeof ejercicio" + i) !== "undefined") {
			eval("ejercicio" + i)();
		}
		let res = {
			text: "",
			write: function (s, t) {
				if (t != undefined) {
					if (t) s = "<span style='color:green'>" + s + "</span>";
					else s = "<span style='color:red'>" + s + "</span>";
				}
				s += "\n";
				this.text += s;
			},
		};
		try {
			f(res);
		} catch (e) {
			fail(i, e);
		}
		return res.text;
	};
}
