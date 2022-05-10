import itertools
from sage.combinat.subset import SubsetsSorted

def basis(n, deg):
    r"""La base standard para L^{\otimes deg+1}([n]) = E_0^{n, deg-n+1}.
    Este método tiene sentido para 1 <= n, 0 <= deg <= n-1."""
    b = []
    for comp in Compositions(n, length=1+deg):
        for perm in Permutations(n):
            cur = []
            ind = 0
            for i in range(1+deg):
                cur.append(perm[ind:ind+comp[i]])
                ind += comp[i]
            b.append(cur)
    return b


def comult(elt):
    r"""Comultiplica un elemento básico de L([n]), representado como una lista de números sin repeticiones."""
    res = []
    n = len(elt)
    r = range(n)
    for sset in sage.combinat.subset.SubsetsSorted(r):
        if len(sset) != 0 and len(sset) != n:
            comp = [i for i in r if i not in sset]
            res.append([[elt[i] for i in sset], [elt[i] for i in comp]])
    return res


def complex(n):
    r"""El espacio vectorial graduado
    \Sigma^n_{\bullet} = L^{\otimes \bullet}([n]),
    presentado como una lista ordenada de bases. Este método tiene sentido para 1 <= n."""
    return [basis(n, i) for i in range(n)]


def differentiate(elt, codomain_basis=[]):
    r"""Si elt es un elemento básico de L^{\otimes k}([n]),
    este método devuelve las coordenadas de la
    aplicación de la diferencial sobre elt en términos de la base standard.
    La base del codominio puede pasarse como parámetro opcional, para ahorrar tiempo
    de ejecución si van a calcularse muchos valores de la diferencial."""
    k = len(elt)
    if not codomain_basis:
        n = max([item for sublist in elt for item in sublist])
        codomain_basis = basis(n, k)
    res = [0 for _ in range(len(codomain_basis))]
    sign = 1
    for i in range(k):
        if len(elt[i]) != 1:
            for term in comult(elt[i]):
                cur = elt[:i] + term + elt[i+1:]
                res[codomain_basis.index(cur)] += sign
        sign *= -1
    return res


def differential(n, deg):
    r"""La diferencial E_0^{n, deg-n} -> E_0^{n, deg-n+1}, como matriz."""
    rows = []
    domain_basis = basis(n, deg-1)
    codomain_basis = basis(n, deg)
    for basic_elt in domain_basis:
        rows.append(differentiate(basic_elt, codomain_basis))
    return matrix(QQ, rows).transpose()


class Formal_combination:
    r'''Una clase para representar e imprimir combinaciones lineales de forma práctica.'''

    def __init__(self, basis, coords):
        self.basis = basis
        self.coords = coords

    def __repr__(self):
        rep = ''
        for (i, coord) in enumerate(self.coords):
            if coord != 0:
                if coord != 1:
                    rep += str(coord) + ' * '
                rep += str(self.basis[i]) + ' + '
        if rep != '':
            return rep[:-3]
        return rep

    def permute(self, permutation):
        r'''Aplica una permutación (presentada como lista de valores) a una combinación formal
        de elementos básicos.'''
        new_coords = [0 for i in range(len(self.coords))]
        for (i, coord) in enumerate(self.coords):
            if coord != 0:
                permuted_basic_elt = []
                for part in self.basis[i]:
                    permuted_basic_elt.append([permutation[i-1] for i in part])
                new_coords[self.basis.index(permuted_basic_elt)] = coord
        return Formal_combination(self.basis, new_coords)


def get_homology_basis(n, deg):
    r'''Devuelve una base de E_1^{n, -deg} como objetos de tipo Formal_combination.'''
    k = n-1-deg
    ch = ChainComplex([differential(n, i) for i in range(1, n)])
    return [Formal_combination(basis(n, k), chain[1].vector(k)) for chain in ch.homology(generators=True)[k]]


def eval_top_character(n, permutation):
    r'''Calcula el valor del caracter de E_1^{n,-n+1} en una permutación específica.'''
    top_basis = get_homology_basis(n, n-1)
    return matrix([elt.permute(permutation).coords[:factorial(n-1)] for elt in top_basis]).trace()


def get_top_character(n):
    r'''Devuelve el valor del caracter de E_1^{n,-n+1}. La lógica para este caso está separada de los demás,
    dado que este espacio es simplemente un subespacio y no un subcociente.'''
    G = SymmetricGroup(n)
    conjugacy_classes = [perm.representative().tuple()
                         for perm in G.conjugacy_classes()]
    return ClassFunction(G, [eval_top_character(n, perm) for perm in conjugacy_classes])


def get_character(n, deg):
    r'''Calcula el caracter del Sn-módulo E_1^{n, -deg} si 0 <= deg <= n-1.
    Este valor se devuelve como un objeto ClassFunction de SageMath.'''
    deg = n-1-deg
    if deg == 0:
        return get_top_character(n)
    G = SymmetricGroup(n)
    conjugacy_classes = [perm.representative().tuple()
                         for perm in G.conjugacy_classes()]

    cycles = differential(n, deg+1).transpose().kernel().basis()
    boundaries = differential(n, deg).transpose().image().basis()
    boundaries_followed_by_cycles = list(boundaries)
    for v in cycles:
        if v not in span(boundaries_followed_by_cycles):
            boundaries_followed_by_cycles.append(v)
    homology_basis = boundaries_followed_by_cycles[len(boundaries):]

    def act_by_perm(coords, perm):
        r'''Calcula la acción permutación de perm sobre un elemento de la base standard expresado en coordenadas.'''
        # Primero obtenemos las coordenadas del elemento permutado en la base standard
        formal_elt = Formal_combination(basis(n, deg), coords)
        permuted_coords = formal_elt.permute(perm).coords
        # El resultado sigue perteneciendo al espacio de ciclos, pero lo podemos escribir como una suma
        # entre un borde y una combinación lineal de nuestra base para la homología. Para obtener
        # las coordenadas del elemento en la homología, basta con obtener las coordenadas de su representante
        # en una base del espacio de ciclos conformada por una base del espacio de bordes seguido de nuestra
        # base para la homología y simplemente olvidarnos de las primeras coordenadas.
        V = QQ ^ (len(homology_basis[0]))
        coords_in_cycles = V.subspace_with_basis(
            boundaries_followed_by_cycles).coordinate_vector(permuted_coords)
        coords_in_homology = coords_in_cycles[len(boundaries):]
        return coords_in_homology

    def char_value(perm):
        r'''Calcula el valor del caracter correspondiente en una permutación dada.'''
        mtx = []
        for elt in homology_basis:
            mtx.append(act_by_perm(elt, perm))
        return matrix(mtx).trace()

    return ClassFunction(G, [char_value(perm) for perm in conjugacy_classes])
