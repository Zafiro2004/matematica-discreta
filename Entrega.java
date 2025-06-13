package entregadiscreta;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.function.BiFunction;
import java.util.function.BiPredicate;
import java.util.function.BooleanSupplier;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.IntStream;

/*
 * Aquesta entrega consisteix en implementar tots els mètodes anomenats "exerciciX". Ara mateix la
 * seva implementació consisteix en llançar `UnsupportedOperationException`, ho heu de canviar així
 * com els aneu fent.
 *
 * Criteris d'avaluació:
 *
 * - Si el codi no compila tendreu un 0.
 *
 * - Les úniques modificacions que podeu fer al codi són:
 *    + Afegir un mètode (dins el tema que el necessiteu)
 *    + Afegir proves a un mètode "tests()"
 *    + Òbviament, implementar els mètodes que heu d'implementar ("exerciciX")
 *   Si feu una modificació que no sigui d'aquesta llista, tendreu un 0.
 *
 * - Principalment, la nota dependrà del correcte funcionament dels mètodes implementats (provant
 *   amb diferents entrades).
 *
 * - Tendrem en compte la neteja i organització del codi. Un estandard que podeu seguir és la guia
 *   d'estil de Google per Java: https://google.github.io/styleguide/javaguide.html . Per exemple:
 *    + IMPORTANT: Aquesta entrega està codificada amb UTF-8 i finals de línia LF.
 *    + Indentació i espaiat consistent
 *    + Bona nomenclatura de variables
 *    + Declarar les variables el més aprop possible al primer ús (és a dir, evitau blocs de
 *      declaracions).
 *    + Convé utilitzar el for-each (for (int x : ...)) enlloc del clàssic (for (int i = 0; ...))
 *      sempre que no necessiteu l'índex del recorregut. Igualment per while si no és necessari.
 *
 * Per com està plantejada aquesta entrega, no necessitau (ni podeu) utilitzar cap `import`
 * addicional, ni qualificar classes que no estiguin ja importades. El que sí podeu fer és definir
 * tots els mètodes addicionals que volgueu (de manera ordenada i dins el tema que pertoqui).
 *
 * Podeu fer aquesta entrega en grups de com a màxim 3 persones, i necessitareu com a minim Java 10.
 * Per entregar, posau els noms i cognoms de tots els membres del grup a l'array `Entrega.NOMS` que
 * està definit a la línia 53.
 *
 * L'entrega es farà a través d'una tasca a l'Aula Digital que obrirem abans de la data que se us
 * hagui comunicat. Si no podeu visualitzar bé algun enunciat, assegurau-vos de que el vostre editor
 * de texte estigui configurat amb codificació UTF-8.
 */
class Entrega {

    static final String[] NOMS = {"Alex De Dios Pallicer"};

    /*
   * Aquí teniu els exercicis del Tema 1 (Lògica).
     */
    static class Tema1 {

        /*
     * Determinau si l'expressió és una tautologia o no:
     *
     * (((vars[0] ops[0] vars[1]) ops[1] vars[2]) ops[2] vars[3]) ...
     *
     * Aquí, vars.length == ops.length+1, i cap dels dos arrays és buid. Podeu suposar que els
     * identificadors de les variables van de 0 a N-1, i tenim N variables diferents (mai més de 20
     * variables).
     *
     * Cada ops[i] pot ser: CONJ, DISJ, IMPL, NAND.
     *
     * Retornau:
     *   1 si és una tautologia
     *   0 si és una contradicció
     *   -1 en qualsevol altre cas.
     *
     * Vegeu els tests per exemples.
         */
        static final char CONJ = '∧';
        static final char DISJ = '∨';
        static final char IMPL = '→';
        static final char NAND = '.';

        static int exercici1(char[] ops, int[] vars) {
            // Primero averiguo cuántas variables hay
            int nVars = 0;
            for (int v : vars) {
                if (v + 1 > nVars) {
                    nVars = v + 1;
                }
            }
            // Uso dos booleanas para saber si siempre es cierto o siempre es falso
            boolean siempreTrue = true;
            boolean siempreFalse = true;
            // Recorro todas las combinaciones posibles de valores de las variables
            for (int j = 0; j < (1 << nVars); j++) {
                boolean[] vals = new boolean[nVars];
                for (int i = 0; i < nVars; i++) {
                    vals[i] = ((j >> i) & 1) == 1;
                }

                // Empiezo evaluando la primera variable
                boolean res = vals[vars[0]];
                // Aplico cada operador con la siguiente variable
                for (int i = 0; i < ops.length; i++) {
                    boolean b = vals[vars[i + 1]];
                    switch (ops[i]) {
                        case CONJ ->
                            res = res && b;  // CONJ
                        case DISJ ->
                            res = res || b;  // DISJ
                        case IMPL ->
                            res = (!res) || b;  // IMPL
                        case NAND ->
                            res = !(res && b);  // NAND
                    }
                }
                // Si alguna vez es falso, no es tautología
                if (!res) {
                    siempreTrue = false;
                }
                // Si alguna vez es cierto, no es contradicción
                if (res) {
                    siempreFalse = false;
                }
            }
            // Devuelvo 1 si es tautología, 0 si es contradicción, -1 si ninguna de las dos
            if (siempreTrue) {
                return 1;
            }
            if (siempreFalse) {
                return 0;
            }
            return -1;
        }

        /*
     * Aquest mètode té de paràmetre l'univers (representat com un array) i els predicats
     * adients `p` i `q`. Per avaluar aquest predicat, si `x` és un element de l'univers, podeu
     * fer-ho com `p.test(x)`, que té com resultat un booleà (true si `P(x)` és cert).
     *
     * Amb l'univers i els predicats `p` i `q` donats, returnau true si la següent proposició és
     * certa.
     *
     * (∀x : P(x)) <-> (∃!x : Q(x))
         */
        static boolean exercici2(int[] universe, Predicate<Integer> p, Predicate<Integer> q) {
            // Voy a comprobar si (para todo x, P(x)) es equivalente a (existe un único x, Q(x))

            // Primero, miro si P(x) se cumple para todos los elementos del universo
            boolean pCumple = true;
            for (int x : universe) {
                if (!p.test(x)) {
                    pCumple = false; // Si falla para uno, ya no es para todos
                    break; // Ya no necesito seguir mirando
                }
            }

            // Ahora, miro si existe un único elemento que cumpla Q(x)
            int contQ = 0; // Cuento cuántos elementos cumplen Q(x)
            for (int x : universe) {
                if (q.test(x)) {
                    contQ++; // Encontré uno que cumple Q(x)
                }
            }
            boolean existeUnicoQ = (contQ == 1); // Debe haber exactamente uno

            // La proposición es cierta si ambos son ciertos o ambos son falsos
            return (pCumple == existeUnicoQ);
        }

        static void tests() {
            // Exercici 1
            System.out.println("\nExercici 1:");
            // Taules de veritat

            // Tautologia: ((p0 → p2) ∨ p1) ∨ p0
            test(1, 1, 1, () -> exercici1(new char[]{IMPL, DISJ, DISJ}, new int[]{0, 2, 1, 0}) == 1);

            // Contradicció: (p0 . p0) ∧ p0
            test(1, 1, 2, () -> exercici1(new char[]{NAND, CONJ}, new int[]{0, 0, 0}) == 0);

            // Más tests
            System.out.println("\nTests Extra:");
            // Tautología simple: p0 -> p0
            test(1, 1, 3, () -> exercici1(new char[]{IMPL}, new int[]{0, 0}) == 1);

            // Ni tautología ni contradicción: p0
            test(1, 1, 4, () -> exercici1(new char[]{}, new int[]{0}) == -1);

            // (p0 ∨ p1) -> p0
            test(1, 1, 5, () -> exercici1(new char[]{DISJ, IMPL}, new int[]{0, 1, 0}) == -1);
            //Modus Ponens: ((p0 → p1) ∧ p0) → p1
            test(1, 1, 6, () -> exercici1(new char[]{IMPL, CONJ, IMPL}, new int[]{0, 1, 0, 1}) == 1);
            //Indeterminación: p0 → p1
            test(1, 1, 7, () -> exercici1(new char[]{IMPL}, new int[]{0, 1}) == -1);
            //Expresión con 5 variables y operadores mixtos (ni tautología ni contradicción)
            test(1, 1, 8, () -> exercici1(new char[]{CONJ, DISJ, IMPL, NAND}, new int[]{0, 1, 2, 3, 4}) == -1);
            //Tautología con DISJ repetido (p0 ∨ p1) ∨ p2
            test(1, 1, 9, () -> exercici1(new char[]{DISJ, DISJ}, new int[]{0, 1, 2}) == -1);

            // Exercici 2
            System.out.println("\nExercici 2:");
            // Equivalència
            test(1, 2, 1, () -> {
                return exercici2(new int[]{1, 2, 3}, (x) -> x == 0, (x) -> x == 0);
            });

            test(1, 2, 2, () -> {
                return exercici2(new int[]{1, 2, 3}, (x) -> x >= 1, (x) -> x % 2 == 0);
            });

            // Más tests 
            System.out.println("\nTests Extra:");
            // P(x) se cumple para todos, Q(x) se cumple para un único elemento
            test(1, 2, 3, () -> exercici2(new int[]{1, 2, 3}, (x) -> true, (x) -> x == 2));
            //P(x) es falso para todos, Q(x) no tiene exactamente un cumplimiento
            test(1, 2, 5, () -> exercici2(new int[]{1, 2, 3}, (x) -> false, (x) -> x > 1));
            //P(x) se cumple para todos, Q(x) se cumple para exactamente uno
            test(1, 2, 6, () -> exercici2(new int[]{1, 2, 3, 4}, (x) -> x > 0, (x) -> x == 3));
            //Ambos lados son falsos (P(x) no se cumple para todos, Q(x) no tiene único cumplimiento)
            test(1, 2, 7, () -> exercici2(new int[]{1, 2, 3}, (x) -> x > 2, (x) -> x >= 1));
            //Universo con un solo elemento
            test(1, 2, 8, () -> exercici2(new int[]{1}, (x) -> x == 1, (x) -> x == 1));
        }
    }

    /*
   * Aquí teniu els exercicis del Tema 2 (Conjunts).
   *
   * Per senzillesa tractarem els conjunts com arrays (sense elements repetits). Per tant, un
   * conjunt de conjunts d'enters tendrà tipus int[][]. Podeu donar per suposat que tots els
   * arrays que representin conjunts i us venguin per paràmetre estan ordenats de menor a major.
   *
   * Les relacions també les representarem com arrays de dues dimensions, on la segona dimensió
   * només té dos elements. L'array estarà ordenat lexicogràficament. Per exemple
   *   int[][] rel = {{0,0}, {0,1}, {1,1}, {2,2}};
   * i també donarem el conjunt on està definida, per exemple
   *   int[] a = {0,1,2};
   * Als tests utilitzarem extensivament la funció generateRel definida al final (també la podeu
   * utilitzar si la necessitau).
   *
   * Les funcions f : A -> B (on A i B son subconjunts dels enters) les representam o bé amb el seu
   * graf o bé amb un objecte de tipus Function<Integer, Integer>. Sempre donarem el domini int[] a
   * i el codomini int[] b. En el cas de tenir un objecte de tipus Function<Integer, Integer>, per
   * aplicar f a x, és a dir, "f(x)" on x és d'A i el resultat f.apply(x) és de B, s'escriu
   * f.apply(x).
     */
    static class Tema2 {

        /*
     * Trobau el nombre de particions diferents del conjunt `a`, que podeu suposar que no és buid.
     *
     * Pista: Cercau informació sobre els nombres de Stirling.
         */
        static int exercici1(int[] a) {
            int n = a.length;
            int[] part = new int[n + 1];
            part[0] = 1;
            for (int i = 1; i <= n; i++) {
                part[i] = 0;
                for (int j = 0; j < i; j++) {
                    part[i] += binom(i - 1, j) * part[j];
                }
            }
            return part[n];
        }

        static int binom(int n, int k) {
            if (k < 0 || k > n) {
                return 0;
            }
            int res = 1;
            for (int i = 1; i <= k; i++) {
                res = res * (n - i + 1) / i;
            }
            return res;
        }

        /*
     * Trobau el cardinal de la relació d'ordre parcial sobre `a` més petita que conté `rel` (si
     * existeix). En altres paraules, el cardinal de la seva clausura reflexiva, transitiva i
     * antisimètrica.
     *
     * Si no existeix, retornau -1.
         */
        static int exercici2(int[] a, int[][] rel) {
            int n = a.length;
            int[][] clausura = new int[n][n];
            // Inicializa la matriz de adyacencia
            for (int i = 0; i < n; i++) {
                clausura[i][i] = 1;
            }
            for (int[] par : rel) {
                int x = Arrays.binarySearch(a, par[0]);
                int y = Arrays.binarySearch(a, par[1]);
                if (x >= 0 && y >= 0) {
                    clausura[x][y] = 1;
                }
            }
            // Clausura transitiva 
            for (int k = 0; k < n; k++) {
                for (int i = 0; i < n; i++) {
                    for (int j = 0; j < n; j++) {
                        if (clausura[i][k] == 1 && clausura[k][j] == 1) {
                            clausura[i][j] = 1;
                        }
                    }
                }
            }
            // Antisimetría: si clausura[i][j] == 1 && clausura[j][i] == 1 && i != j => no es orden parcial
            for (int i = 0; i < n; i++) {
                for (int j = 0; j < n; j++) {
                    if (i != j && clausura[i][j] == 1 && clausura[j][i] == 1) {
                        return -1;
                    }
                }
            }
            // Cuenta el número de pares en la clausura
            int count = 0;
            for (int i = 0; i < n; i++) {
                for (int j = 0; j < n; j++) {
                    if (clausura[i][j] == 1) {
                        count++;
                    }
                }
            }
            return count;
        }

        /*
     * Donada una relació d'ordre parcial `rel` definida sobre `a` i un subconjunt `x` de `a`,
     * retornau:
     * - L'ínfim de `x` si existeix i `op` és false
     * - El suprem de `x` si existeix i `op` és true
     * - null en qualsevol altre cas
         */
        static Integer exercici3(int[] a, int[][] rel, int[] x, boolean op) {
            int n = a.length;
            boolean[][] mat = new boolean[n][n];
            for (int[] par : rel) {
                int i = Arrays.binarySearch(a, par[0]);
                int j = Arrays.binarySearch(a, par[1]);
                mat[i][j] = true;
            }
            // Clausura transitiva
            for (int k = 0; k < n; k++) {
                for (int i = 0; i < n; i++) {
                    for (int j = 0; j < n; j++) {
                        mat[i][j] |= (mat[i][k] && mat[k][j]);
                    }
                }
            }
            List<Integer> candidates = new ArrayList<>();
            for (int i = 0; i < n; i++) {
                boolean valid = true;
                for (int xi : x) {
                    int j = Arrays.binarySearch(a, xi);
                    if (op) { // supremo: a[i] >= xi para todo xi
                        if (!mat[j][i]) {
                            valid = false;
                        }
                    } else { // ínfimo: a[i] <= xi para todo xi
                        if (!mat[i][j]) {
                            valid = false;
                        }
                    }
                }
                if (valid) {
                    candidates.add(a[i]);
                }
            }
            // Elegir el mínimo (para supremo) o máximo (para ínfimo) de los candidatos
            Integer res = null;
            for (int v : candidates) {
                boolean isBest = true;
                for (int u : candidates) {
                    if (u == v) {
                        continue;
                    }
                    int i = Arrays.binarySearch(a, v);
                    int j = Arrays.binarySearch(a, u);
                    if (op) { // supremo: buscamos el mínimo
                        if (mat[i][j]) {
                            isBest = false;
                        }
                    } else { // ínfimo: buscamos el máximo
                        if (mat[j][i]) {
                            isBest = false;
                        }
                    }
                }
                if (isBest) {
                    if (res != null) {
                        return null; // no único
                    }
                    res = v;
                }
            }
            return res;
        }

        /*
     * Donada una funció `f` de `a` a `b`, retornau:
     *  - El graf de la seva inversa (si existeix)
     *  - Sinó, el graf d'una inversa seva per l'esquerra (si existeix)
     *  - Sinó, el graf d'una inversa seva per la dreta (si existeix)
     *  - Sinó, null.
         */
        static int[][] exercici4(int[] a, int[] b, Function<Integer, Integer> f) {
            // 1. Calcular el grafo de la función f
            int[][] grafo = new int[a.length][2];
            for (int i = 0; i < a.length; i++) {
                grafo[i][0] = a[i];
                grafo[i][1] = f.apply(a[i]);
            }

            // 2. Comprobar si es biyectiva (para inversa normal)
            boolean inyect = true;
            boolean sobreyect = true;
            boolean[] vistos = new boolean[b.length]; // Para comprobar sobreyectividad
            Arrays.fill(vistos, false); // Inicializar todos los elementos como no vistos

            for (int i = 0; i < a.length; i++) {
                int imagen = grafo[i][1];
                boolean encontrado = false;
                for (int j = 0; j < b.length; j++) {
                    if (b[j] == imagen) {
                        if (vistos[j]) {
                            inyect = false; // No es inyectiva
                        }
                        vistos[j] = true;
                        encontrado = true;
                        break;
                    }
                }
                if (!encontrado) {
                    sobreyect = false; // No es sobreyectiva
                }
            }

            // Verificar si todos los elementos de 'b' fueron vistos
            for (boolean visto : vistos) {
                if (!visto) {
                    sobreyect = false; // No es sobreyectiva
                    break;
                }
            }

            if (inyect && sobreyect && a.length == b.length) {
                // Es biyectiva:  Inversa normal
                int[][] inversa = new int[a.length][2];
                for (int i = 0; i < a.length; i++) {
                    inversa[i][0] = grafo[i][1]; // Intercambiar dominio y codominio
                    inversa[i][1] = grafo[i][0];
                }
                return lexSorted(inversa);
            }

            // 3. Si no es biyectiva, intentar inversa por la derecha
            if (sobreyect) {
                // Inversa por la derecha:  f(g(y)) = y  para todo y en B
                int[][] invDer = new int[b.length][2];
                for (int i = 0; i < b.length; i++) {
                    int y = b[i]; // Elemento del codominio
                    boolean encontrado = false;
                    for (int j = 0; j < a.length; j++) {
                        if (f.apply(a[j]).equals(y)) {  // f(x) == y
                            invDer[i][0] = y;  // g(y) = x
                            invDer[i][1] = a[j];
                            encontrado = true;
                            break;
                        }
                    }
                    if (!encontrado) {
                        return null; // No existe inversa por la derecha
                    }
                }
                return lexSorted(invDer);
            }

            // 4. Si no es sobreyectiva, intentar inversa por la izquierda
            if (inyect) {
                // Inversa por la izquierda: g: B -> A
                int[][] invIzq = new int[b.length][2];
                for (int i = 0; i < b.length; i++) {
                    int y = b[i];
                    Integer gx = null;
                    // Buscamos x en a tal que f(x) == y
                    for (int x : a) {
                        if (f.apply(x).equals(y)) {
                            gx = x;
                            break;
                        }
                    }
                    if (gx == null) {
                        // Para valores fuera de la imagen, asignamos un elemento arbitrario de a
                        gx = a[0];
                    }
                    invIzq[i][0] = y;
                    invIzq[i][1] = gx;
                }
                return lexSorted(invIzq);
            }

            // 5. Si no hay inversa, devolver null
            return null;
        }

        /*
     * Aquí teniu alguns exemples i proves relacionades amb aquests exercicis (vegeu `main`)
         */
        static void tests() {
            // Exercici 1
            System.out.println("\nExercici 1:");
            // Nombre de particions

            test(2, 1, 1, () -> exercici1(new int[]{1}) == 1);
            test(2, 1, 2, () -> exercici1(new int[]{1, 2, 3}) == 5);
            //Mas tests
            System.out.println("\nTests Extra:");
            //Conjunto con 4 elementos (esperado: 15 particiones)
            test(2, 1, 3, () -> exercici1(new int[]{1, 2, 3, 4}) == 15);
            //Conjunto con 2 elementos (esperado: 2 particiones)
            test(2, 1, 4, () -> exercici1(new int[]{1, 2}) == 2);
            //Conjunto con 5 elementos (esperado: 52 particiones)
            test(2, 1, 5, () -> exercici1(new int[]{1, 2, 3, 4, 5}) == 52);

            // Exercici 2
            System.out.println("\nExercici 2:");
            // Clausura d'ordre parcial
            final int[] INT02 = {0, 1, 2};

            test(2, 2, 1, () -> exercici2(INT02, new int[][]{{0, 1}, {1, 2}}) == 6);
            test(2, 2, 2, () -> exercici2(INT02, new int[][]{{0, 1}, {1, 0}, {1, 2}}) == -1);
            //Mas tests
            System.out.println("\nTests Extra:");
            //Relación vacía (solo reflexiva en la clausura)
            test(2, 2, 3, () -> exercici2(new int[]{0, 1}, new int[][]{}) == 2);
            //Relación completa (orden total)
            test(2, 2, 4, () -> exercici2(new int[]{0, 1, 2}, new int[][]{{0, 1}, {0, 2}, {1, 2}}) == 6);
            //Relación con ciclo (no es orden parcial)
            test(2, 2, 5, () -> exercici2(new int[]{0, 1, 2}, new int[][]{{0, 1}, {1, 2}, {2, 0}}) == -1);

            // Exercici 3
            System.out.println("\nExercici 3:");
            // Ínfims i suprems
            final int[] INT15 = {1, 2, 3, 4, 5};
            final int[][] DIV15 = generateRel(INT15, (n, m) -> m % n == 0);
            final Integer ONE = 1;

            test(2, 3, 1, () -> ONE.equals(exercici3(INT15, DIV15, new int[]{2, 3}, false)));
            test(2, 3, 2, () -> exercici3(INT15, DIV15, new int[]{2, 3}, true) == null);
            //Mas tests
            System.out.println("\nTests Extra:");
            //Subconjunto vacío (supremo debe ser el mínimo elemento, si existe)
            test(2, 3, 3, () -> exercici3(INT15, DIV15, new int[]{}, true) == null);

            //Orden total, ínfimo de un subconjunto
            test(2, 3, 4, () -> Integer.valueOf(1).equals(exercici3(new int[]{1, 2, 3}, generateRel(new int[]{1, 2, 3}, (n, m) -> n <= m), new int[]{2, 3}, false)));

            // Exercici 4
            System.out.println("\nExercici 4:");
            // Inverses
            final int[] INT05 = {0, 1, 2, 3, 4, 5};

            test(2, 4, 1, () -> {
                var inv = exercici4(INT05, INT02, (x) -> x / 2);

                if (inv == null) {
                    return false;
                }

                inv = lexSorted(inv);

                if (inv.length != INT02.length) {
                    return false;
                }

                for (int i = 0; i < INT02.length; i++) {
                    if (inv[i][0] != i || inv[i][1] / 2 != i) {
                        return false;
                    }
                }

                return true;
            });

            test(2, 4, 2, () -> {
                var inv = exercici4(INT02, INT05, (x) -> x);

                if (inv == null) {
                    return false;
                }

                inv = lexSorted(inv);

                if (inv.length != INT05.length) {
                    return false;
                }

                for (int i = 0; i < INT02.length; i++) {
                    if (inv[i][0] != i || inv[i][1] != i) {
                        return false;
                    }
                }

                return true;
            });
        }

        /*
     * Ordena lexicogràficament un array de 2 dimensions
     * Per exemple:
     *  arr = {{1,0}, {2,2}, {0,1}}
     *  resultat = {{0,1}, {1,0}, {2,2}}
         */
        static int[][] lexSorted(int[][] arr) {
            if (arr == null) {
                return null;
            }

            var arr2 = Arrays.copyOf(arr, arr.length);
            Arrays.sort(arr2, Arrays::compare);
            return arr2;
        }

        /*
     * Genera un array int[][] amb els elements {a, b} (a de as, b de bs) que satisfàn pred.test(a, b)
     * Per exemple:
     *   as = {0, 1}
     *   bs = {0, 1, 2}
     *   pred = (a, b) -> a == b
     *   resultat = {{0,0}, {1,1}}
         */
        static int[][] generateRel(int[] as, int[] bs, BiPredicate<Integer, Integer> pred) {
            var rel = new ArrayList<int[]>();

            for (int a : as) {
                for (int b : bs) {
                    if (pred.test(a, b)) {
                        rel.add(new int[]{a, b});
                    }
                }
            }

            return rel.toArray(new int[][]{});
        }

        // Especialització de generateRel per as = bs
        static int[][] generateRel(int[] as, BiPredicate<Integer, Integer> pred) {
            return generateRel(as, as, pred);
        }
    }

    /*
   * Aquí teniu els exercicis del Tema 3 (Grafs).
   *
   * Els (di)grafs vendran donats com llistes d'adjacència (és a dir, tractau-los com diccionaris
   * d'adjacència on l'índex és la clau i els vèrtexos estan numerats de 0 a n-1). Per exemple,
   * podem donar el graf cicle no dirigit d'ordre 3 com:
   *
   * int[][] c3dict = {
   *   {1, 2}, // veïns de 0
   *   {0, 2}, // veïns de 1
   *   {0, 1}  // veïns de 2
   * };
     */
    static class Tema3 {

        /*
     * Determinau si el graf `g` (no dirigit) té cicles.
         */
        static boolean exercici1(int[][] g) {
            // Usaré una búsqueda en profundidad (DFS) para detectar ciclos.
            int n = g.length;
            boolean[] visitado = new boolean[n];
            // Recorro todos los nodos para asegurarme de cubrir grafos desconectados
            for (int i = 0; i < n; i++) {
                if (!visitado[i]) {
                    if (tieneCiclo(g, i, -1, visitado)) {
                        return true; // Se encontró un ciclo
                    }
                }
            }
            return false; // No encontré ciclos
        }

        // Método auxiliar para la búsqueda en profundidad
        static boolean tieneCiclo(int[][] g, int nodo, int padre, boolean[] visitado) {
            visitado[nodo] = true; // Marco el nodo como visitado
            // Recorro los vecinos del nodo actual
            for (int vecino : g[nodo]) {
                // Si el vecino no ha sido visitado, lo visito recursivamente
                if (!visitado[vecino]) {
                    if (tieneCiclo(g, vecino, nodo, visitado)) {
                        return true; // Ciclo en la rama
                    }
                } // Si el vecino es el padre, lo ignoro (no es un ciclo)
                else if (vecino != padre) {
                    return true; // Se encontró un cilo
                }
            }
            return false; // No encontré ciclos desde este nodo
        }

        /*
     * Determinau si els dos grafs són isomorfs. Podeu suposar que cap dels dos té ordre major que
     * 10.
         */
        static boolean exercici2(int[][] g1, int[][] g2) {
            // Si tienen diferente número de nodos, no pueden ser isomorfos
            if (g1.length != g2.length) {
                return false;
            }

            int n = g1.length;

            // Intentaré todas las posibles permutaciones de nodos de g2
            int[] perm = new int[n];
            for (int i = 0; i < n; i++) {
                perm[i] = i; // Inicialmente, la permutación es la identidad
            }

            // Genero permutaciones hasta que encuentre una que haga los grafos iguales, o hasta probar todas
            do {
                // Compruebo si la permutación actual hace que los grafos sean iguales
                if (igualesPerm(g1, g2, perm)) {
                    return true; // Son isomorfos
                }
            } while (genPerm(perm));

            // Si probé todas las permutaciones y ninguna funcionó, no son isomorfos
            return false;
        }

        // Método auxiliar para comprobar si los grafos son iguales con una permutación dada
        static boolean igualesPerm(int[][] g1, int[][] g2, int[] perm) {
            int n = g1.length;
            // 1) Cada vértice conserva el mismo grado
            for (int i = 0; i < n; i++) {
                if (g1[i].length != g2[perm[i]].length) {
                    return false;
                }
            }
            // 2) Cada arista de g1 aparece en g2 según la permutación
            for (int i = 0; i < n; i++) {
                for (int vecino : g1[i]) {
                    boolean found = false;
                    for (int v2 : g2[perm[i]]) {
                        if (v2 == perm[vecino]) {
                            found = true;
                            break;
                        }
                    }
                    if (!found) {
                        return false;
                    }
                }
            }
            return true;
        }

        // Método auxiliar para generar la siguiente permutación (algoritmo de Steinhaus-Johnson-Trotter)
        static boolean genPerm(int[] arr) {
            int n = arr.length;

            // Encuentro el mayor índice i tal que arr[i] < arr[i + 1]
            int i = -1;
            for (int j = 0; j < n - 1; j++) {
                if (arr[j] < arr[j + 1]) {
                    i = j;
                }
            }

            // Si no existe tal índice, ya generé todas las permutaciones
            if (i == -1) {
                return false;
            }

            // Encuentro el mayor índice j tal que arr[i] < arr[j]
            int j = i + 1;
            for (int k = i + 1; k < n; k++) {
                if (arr[i] < arr[k]) {
                    j = k;
                }
            }

            // Intercambio arr[i] y arr[j]
            int temp = arr[i];
            arr[i] = arr[j];
            arr[j] = temp;

            // Invierto la sublista desde i + 1 hasta el final
            int inicio = i + 1;
            int fin = n - 1;
            while (inicio < fin) {
                temp = arr[inicio];
                arr[inicio] = arr[fin];
                arr[fin] = temp;
                inicio++;
                fin--;
            }

            return true;
        }

        /*
     * Determinau si el graf `g` (no dirigit) és un arbre. Si ho és, retornau el seu recorregut en
     * postordre desde el vèrtex `r`. Sinó, retornau null;
     *
     * En cas de ser un arbre, assumiu que l'ordre dels fills vé donat per l'array de veïns de cada
     * vèrtex.
         */
        static int[] exercici3(int[][] g, int r) {
            // Primero, verifico si el grafo es un árbol:
            // 1. No debe tener ciclos
            // 2. Debe ser conexo
            if (exercici1(g)) { // Tiene ciclos, no es árbol
                return null;
            }

            int n = g.length;
            boolean[] visitado = new boolean[n];
            int[] post = new int[n];
            int[] ind = {0}; // Para llevar la cuenta de la posición en el array postorden

            // Verifico si es conexo haciendo un recorrido desde el nodo raíz 'r'
            recorrPost(g, r, visitado, post, ind);

            // Si no visité todos los nodos, el grafo no es conexo y, por lo tanto, no es un árbol
            for (boolean v : visitado) {
                if (!v) {
                    return null;
                }
            }

            // Si es un árbol, retorno el recorrido en postorden (quito los elementos no usados)
            return Arrays.copyOf(post, ind[0]);
        }

        // Método auxiliar para realizar el recorrido en postorden
        static void recorrPost(int[][] g, int nodo, boolean[] visitado, int[] post, int[] ind) {
            visitado[nodo] = true; // Marco el nodo como visitado
            // Recorro los vecinos del nodo actual (serán los hijos en el árbol)
            for (int vecino : g[nodo]) {
                if (!visitado[vecino]) { // Si el vecino no ha sido visitado, lo visito recursivamente
                    recorrPost(g, vecino, visitado, post, ind);
                }
            }
            // Después de visitar todos los hijos, agrego el nodo actual al recorrido en postorden
            post[ind[0]++] = nodo;
        }

        /*
     * Suposau que l'entrada és un mapa com el següent, donat com String per files (vegeu els tests)
     *
     *   _____________________________________
     *  |          #       #########      ####|
     *  |       O  # ###   #########  ##  ####|
     *  |    ####### ###   #########  ##      |
     *  |    ####  # ###   #########  ######  |
     *  |    ####    ###              ######  |
     *  |    ######################## ##      |
     *  |    ####                     ## D    |
     *  |_____________________________##______|
     *
     * Els límits del mapa els podeu considerar com els límits de l'array/String, no fa falta que
     * cerqueu els caràcters "_" i "|", i a més podeu suposar que el mapa és rectangular.
     *
     * Donau el nombre mínim de caselles que s'han de recorrer per anar de l'origen "O" fins al
     * destí "D" amb les següents regles:
     *  - No es pot sortir dels límits del mapa
     *  - No es pot passar per caselles "#"
     *  - No es pot anar en diagonal
     *
     * Si és impossible, retornau -1.
         */
        static int exercici4(char[][] mapa) {
            // Encuentro el origen 'O' y el destino 'D'
            int filOrig = -1, colOrig = -1;
            int filDest = -1, colDest = -1;

            for (int i = 0; i < mapa.length; i++) {
                for (int j = 0; j < mapa[i].length; j++) {
                    if (mapa[i][j] == 'O') {
                        filOrig = i;
                        colOrig = j;
                    } else if (mapa[i][j] == 'D') {
                        filDest = i;
                        colDest = j;
                    }
                }
            }

            // Si no encuentro el origen o el destino, retorno -1
            if (filOrig == -1 || filDest == -1) {
                return -1;
            }

            // Utilizo una matriz para rastrear las distancias
            int fil = mapa.length;
            int col = mapa[0].length;
            int[][] dist = new int[fil][col];
            for (int i = 0; i < fil; i++) {
                Arrays.fill(dist[i], -1); // -1 significa no visitado
            }
            dist[filOrig][colOrig] = 0; // Distancia desde el origen al origen es 0

            // Utilizo una lista para los nodos a explorar
            List<Integer> filExpl = new ArrayList<>();
            List<Integer> colExpl = new ArrayList<>();
            filExpl.add(filOrig);
            colExpl.add(colOrig);

            // Movimientos posibles (arriba, abajo, izquierda, derecha)
            int[] dr = {-1, 1, 0, 0};
            int[] dc = {0, 0, -1, 1};

            // Mientras haya nodos para explorar...
            for (int i = 0; i < filExpl.size(); i++) {
                int filAct = filExpl.get(i);
                int colAct = colExpl.get(i);

                // Si llegué al destino, retorno la distancia
                if (filAct == filDest && colAct == colDest) {
                    return dist[filAct][colAct];
                }

                // Exploro los vecinos
                for (int j = 0; j < 4; j++) {
                    int newFil = filAct + dr[j];
                    int newCol = colAct + dc[j];

                    // Verifico si el vecino está dentro de los límites
                    if (newFil >= 0 && newFil < fil && newCol >= 0 && newCol < col) {
                        // Verifico si el vecino no es una pared '#' y no ha sido visitado
                        if (mapa[newFil][newCol] != '#' && dist[newFil][newCol] == -1) {
                            // Agrego el vecino a la lista para explorar y actualizo la distancia
                            filExpl.add(newFil);
                            colExpl.add(newCol);
                            dist[newFil][newCol] = dist[filAct][colAct] + 1;
                        }
                    }
                }
            }

            // Si no encontré un camino al destino, retorno -1
            return -1;
        }


        /*
     * Aquí teniu alguns exemples i proves relacionades amb aquests exercicis (vegeu `main`)
         */
        static void tests() {

            final int[][] D2 = {{}, {}};
            final int[][] C3 = {{1, 2}, {0, 2}, {0, 1}};

            final int[][] T1 = {{1, 2}, {0}, {0}};
            final int[][] T2 = {{1}, {0, 2}, {1}};

            // Exercici 1
            System.out.println("\nExercici 1:");
            // G té cicles?
            test(3, 1, 1, () -> !exercici1(D2));
            test(3, 1, 2, () -> exercici1(C3));

            // Exercici 2
            System.out.println("\nExercici 2:");
            // Isomorfisme de grafs
            test(3, 2, 1, () -> exercici2(T1, T2));
            test(3, 2, 2, () -> !exercici2(T1, C3));

            // Exercici 3
            System.out.println("\nExercici 4:");
            // Postordre
            test(3, 3, 1, () -> exercici3(C3, 1) == null);
            test(3, 3, 2, () -> Arrays.equals(exercici3(T1, 0), new int[]{1, 2, 0}));

            // Exercici 4
            System.out.println("\nExercici 4:");
            // Laberint
            test(3, 4, 1, () -> {
                return -1 == exercici4(new char[][]{
                    " #O".toCharArray(),
                    "D# ".toCharArray(),
                    " # ".toCharArray(),});
            });

            test(3, 4, 2, () -> {
                return 8 == exercici4(new char[][]{
                    "###D".toCharArray(),
                    "O # ".toCharArray(),
                    " ## ".toCharArray(),
                    "    ".toCharArray(),});
            });
        }
    }

    /*
   * Aquí teniu els exercicis del Tema 4 (Aritmètica).
   *
   * En aquest tema no podeu:
   *  - Utilitzar la força bruta per resoldre equacions: és a dir, provar tots els nombres de 0 a n
   *    fins trobar el que funcioni.
   *  - Utilitzar long, float ni double.
   *
   * Si implementau algun dels exercicis així, tendreu un 0 d'aquell exercici.
     */
 /*
 * Implementación de los ejercicios del Tema 4 (Aritmética)
 * Cifrado y descifrado RSA
     */
    static class Tema4 {

        /*
     * Primer, codificau el missatge en blocs de longitud 2 amb codificació ASCII. Després encriptau
     * el missatge utilitzant xifrat RSA amb la clau pública donada.
     *
     * Per obtenir els codis ASCII del String podeu utilitzar `msg.getBytes()`.
     *
     * Podeu suposar que:
     * - La longitud de `msg` és múltiple de 2
     * - El valor de tots els caràcters de `msg` està entre 32 i 127.
     * - La clau pública (n, e) és de la forma vista a les transparències.
     * - n és major que 2¹⁴, i n² és menor que Integer.MAX_VALUE
     *
     * Pista: https://en.wikipedia.org/wiki/Exponentiation_by_squaring
         */
        static int[] exercici1(String msg, int n, int e) {
            //Creamos la variable de bloques encriptados
            int[] BloqEnc = new int[msg.length() / 2];

            for (int i = 0; i < msg.length(); i += 2) {
                // Obtenemos códigos ASCII para dos caracteres consecutivos
                int Cod1 = msg.charAt(i);
                int Cod2 = msg.charAt(i + 1);

                // Combinamos en un bloque de 14 bits: primer carácter (7 bits) | segundo carácter (7 bits)
                int BloqComb = (Cod1 << 7) | Cod2;

                // Ciframos utilizando exponenciación modular
                BloqEnc[i / 2] = modExp(BloqComb, e, n);
            }
            return BloqEnc;
        }


        /*
     * Primer, desencriptau el missatge utilitzant xifrat RSA amb la clau pública donada. Després
     * descodificau el missatge en blocs de longitud 2 amb codificació ASCII (igual que l'exercici
     * anterior, però al revés).
     *
     * Per construir un String a partir d'un array de bytes podeu fer servir el constructor
     * `new String(byte[])`. Si heu de factoritzar algun nombre, ho podeu fer per força bruta.
     *
     * També podeu suposar que:
     * - La longitud del missatge original és múltiple de 2
     * - El valor de tots els caràcters originals estava entre 32 i 127.
     * - La clau pública (n, e) és de la forma vista a les transparències.
     * - n és major que 2¹⁴, i n² és menor que Integer.MAX_VALUE
         */
        static String exercici2(int[] m, int n, int e) {
            // Factorizamos n en numeros primos (p y q)
            int p = numPrim(n);
            int q = n / p;

            // Calculamos la función de Euler
            int phi = (p - 1) * (q - 1);

            // Calcular el la variable para la clave privada (inverso modular de e mod phi)
            int ClavPriv = invMod(e, phi);

            // Preparamos el búfer de salida para los caracteres decodificados
            char[] DecodChar = new char[m.length * 2];
            int bufferIndex = 0;

            for (int BloqEnc : m) {
                // Desencriptamos usando la clave privada
                int BloqDes = modExp(BloqEnc, ClavPriv, n);

                // Dividimos el bloque de 14 bits en caracteres originales de 7 bits.
                DecodChar[bufferIndex++] = (char) (BloqDes >> 7);
                DecodChar[bufferIndex++] = (char) (BloqDes & 0x7F);
            }
            return new String(DecodChar);
        }

// Exponenciación modular eficiente mediante cuadrado y multiplicación
        static int modExp(int base, int exp, int mod) {
            long res = 1;//Variable resultado
            long act = base % mod;//Variable actual

            while (exp > 0) {
                if ((exp & 1) == 1) {
                    res = (res * act) % mod;
                }
                act = (act * act) % mod;
                exp >>= 1;
            }
            return (int) res;
        }

// Algoritmo de Euclides extendido para la inversa modular
        static int invMod(int a, int m) {
            int mod = m;
            int x0 = 0, x1 = 1;

            while (a > 1) {
                int q = a / m;//Variable quociente
                int temp = m;
                m = a % m;
                a = temp;
                temp = x0;
                x0 = x1 - q * x0;
                x1 = temp;
            }
            return x1 < 0 ? x1 + mod : x1;
        }

//Encuentra un factor primo de n 
        static int numPrim(int n) {
            for (int i = 2; i * i <= n; i++) {
                if (n % i == 0) {
                    return i;
                }
            }
            return n; // n es primo si no se encuentran factores
        }

        static void tests() {
            // Exercici 1
            // Codificar i encriptar
            System.out.println("\nExercici 1:");
            test(4, 1, 1, () -> {
                var n = 2 * 8209;
                var e = 5;

                var encr = exercici1("Patata", n, e);
                return Arrays.equals(encr, new int[]{4907, 4785, 4785});

            });
            //Mas tests
            test(4, 1, 2, () -> {
                var n = 101 * 113; // 11413
                var e = 17;
                var encr = exercici1("Hola!!", n, e);
                // Solo probamos que se codifica y el array tiene el tamaño correcto
                return encr.length == 3; // "Hola!!" → 6 caracteres / 2 = 3 bloques
            });

            test(4, 1, 3, () -> {
                var n = 137 * 131; // 17947
                var e = 3;
                var encr = exercici1("AA", n, e); // 'A' = 65
                var bloqueEsperat = modExp((65 << 7) | 65, e, n);
                return encr.length == 1 && encr[0] == bloqueEsperat;
            });

            // Exercici 2
            // Desencriptar i decodificar
            System.out.println("\nExercici 2:");
            test(4, 2, 1, () -> {
                var n = 2 * 8209;
                var e = 5;

                var encr = new int[]{4907, 4785, 4785};
                var decr = exercici2(encr, n, e);
                return "Patata".equals(decr);
            });
            //Mas tests 
            test(4, 2, 2, () -> {
                var n = 137 * 131; // 17947
                var e = 3;
                int bloque = modExp((65 << 7) | 65, e, n); // "AA"
                var decr = exercici2(new int[]{bloque}, n, e);
                return "AA".equals(decr);
            });

            test(4, 2, 3, () -> {
                var n = 149 * 157; // 23413
                var e = 7;
                String original = " !"; // 32 y 33 (mínimos del rango)
                int bloque = modExp((32 << 7) | 33, e, n);
                var decr = exercici2(new int[]{bloque}, n, e);
                return original.equals(decr);
            });

        }
    }

    /*
   * Aquest mètode `main` conté alguns exemples de paràmetres i dels resultats que haurien de donar
   * els exercicis. Podeu utilitzar-los de guia i també en podeu afegir d'altres (no els tendrem en
   * compte, però és molt recomanable).
   *
   * Podeu aprofitar el mètode `test` per comprovar fàcilment que un valor sigui `true`.
     */
    public static void main(String[] args) {
        System.out.println("---- Tema 1 ----");
        Tema1.tests();
        System.out.println("\n---- Tema 2 ----");
        Tema2.tests();
        System.out.println("\n---- Tema 3 ----");
        Tema3.tests();
        System.out.println("\n---- Tema 4 ----");
        Tema4.tests();
    }

    // Informa sobre el resultat de p, juntament amb quin tema, exercici i test es correspon.
    static void test(int tema, int exercici, int test, BooleanSupplier p) {
        try {
            if (p.getAsBoolean()) {
                System.out.printf("Tema %d, exercici %d, test %d: OK\n", tema, exercici, test);
            } else {
                System.out.printf("Tema %d, exercici %d, test %d: Error\n", tema, exercici, test);
            }
        } catch (Exception e) {
            if (e instanceof UnsupportedOperationException && "pendent".equals(e.getMessage())) {
                System.out.printf("Tema %d, exercici %d, test %d: Pendent\n", tema, exercici, test);
            } else {
                System.out.printf("Tema %d, exercici %d, test %d: Excepció\n", tema, exercici, test);
                e.printStackTrace();
            }
        }
    }
}

// vim: set textwidth=100 shiftwidth=2 expandtab :
