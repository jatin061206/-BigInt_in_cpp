/*
 DSA Project 
 Project Title : BIGINT & Calculation of PI
*/

#include <iostream>
#include <iomanip>
#include <vector>
#include <string>
#include <cmath>
#include <ctime>
#include <fstream>
#include <algorithm>

using namespace std;

const unsigned long long BASE = 1000000000000000000ULL; // 1e18
const unsigned long long HALFBASE = 1000000000ULL;
const int MAX_FACT = 10000;

unsigned int decimal_precision = 3000;

const string OUTPUT_SQRT_FILENAME = "./output_sqrt_10005.txt";
const string OUTPUT_PI_FILENAME = "./output_pi.txt";

struct BigIntStruct {
    short int sign;
    unsigned int len;
    unsigned long long *d;

    BigIntStruct(unsigned int length) {
        sign = 1;
        len = length;
        d = new unsigned long long[length]();
    }

    ~BigIntStruct() {
        delete[] d;
    }
};

struct FractionStruct {
    BigIntStruct *num;
    BigIntStruct *den;
};

struct ComplexStruct {
    long long int real;
    long long int imag;

    ComplexStruct() : real(0), imag(0) {}
};

typedef BigIntStruct *BigInt;
typedef ComplexStruct *Complex;
typedef FractionStruct *Fraction;

BigInt FACT[MAX_FACT];
Fraction sqrt_10005 = nullptr;
Fraction PI_val = nullptr;
string PI_str;

// Function prototypes
void set_zero(BigInt b);
void print_BigInt(BigInt b);
BigInt input_BigInt();
BigInt Add(const BigInt a, const BigInt b);
BigInt Subtract(const BigInt a, const BigInt b);
void _MUL_(unsigned long long x, unsigned long long y, unsigned long long &carry, unsigned long long &result);
BigInt Multiply(const BigInt a, const BigInt b);
void Left_Shift(BigInt num, unsigned int shift);
int Compare(const BigInt a, const BigInt b);
BigInt Divide(const BigInt a, const BigInt b, BigInt *remainder);
string Decimal_Division(BigInt a, BigInt b);
BigInt Remainder(BigInt a, BigInt b);
BigInt Power(BigInt num, unsigned long long p);
BigInt GCD(BigInt a, BigInt b);
BigInt Factorial(unsigned long long n);
void precompute_factorial();
void Increment(const BigInt a, const BigInt delta);
void increase_size(BigInt b, const unsigned int delta_len);
void remove_preceding_zeroes(BigInt a);
int isPrime(int n);
int gcd(int a, int b);

Complex new_Complex();
void print_Complex(Complex a);
long long int real_part(Complex a);
long long int imag_part(Complex a);
long long int complex_modulus(Complex a); // Renamed from modulus to avoid std::modulus conflict
Complex conjugate(Complex a);
Complex add_Complex(Complex a, Complex b);
Complex subtract_Complex(Complex a, Complex b);
Complex multiply_Complex(Complex a, Complex b);
Complex divide_Complex(Complex a, Complex b);

Fraction new_Fraction();
Fraction input_Fraction();
void print_Fraction(Fraction a);
void reduce_Fraction(Fraction a);
Fraction add_Fraction(Fraction a, Fraction b);
Fraction subtract_Fraction(Fraction a, Fraction b);
Fraction multiply_Fraction(Fraction a, Fraction b);
Fraction divide_Fraction(Fraction a, Fraction b);
void reciprocal_Fraction(Fraction a);
void free_Fraction(Fraction a);
void cancel_zeroes(Fraction a);

Fraction Square_Root(BigInt k, int n);
void PI_Chudnovsky(int n);

// -------------- BigInt functions ----------------

void set_zero(BigInt b) {
    for (unsigned int i = 0; i < b->len; i++)
        b->d[i] = 0;
}

void print_BigInt(BigInt b) {
    cout << (b->sign == 1 ? '+' : '-');

    int i = b->len;
    while (--i > 0 && b->d[i] == 0);

    cout << b->d[i--];

    while (i >= 0) {
        cout << setfill('0') << setw(18) << b->d[i--];
    }
    cout << "\n";
}

BigInt input_BigInt() {
    string s;
    cin >> s;
    int sgn = 1;
    int start = 0;

    if (s[0] == '-') { sgn = 0; start = 1; }
    else if (s[0] == '+') { start = 1; }

    int count = (int)s.length() - start;
    int lenreq = count / 18 + (count % 18 != 0 ? 1 : 0);
    if (lenreq == 0) lenreq = 1;

    BigInt x = new BigIntStruct(lenreq);
    x->sign = sgn;
    int j = 0;

    for (int i = s.length(); i > start; i -= 18) {
        int len = min(18, i - start);
        string chunk = s.substr(i - len, len);
        x->d[j++] = stoull(chunk);
    }
    return x;
}

BigInt Add(const BigInt a, const BigInt b) {
    if (a->sign == 1 && b->sign == 0) return Subtract(a, b);
    if (a->sign == 0 && b->sign == 1) return Subtract(b, a);

    BigInt c = new BigIntStruct(1 + max(a->len, b->len));
    unsigned long long carry = 0;

    for (unsigned int i = 0; i < c->len - 1; i++) {
        c->d[i] = carry + (i < a->len ? a->d[i] : 0) + (i < b->len ? b->d[i] : 0);
        carry = c->d[i] / BASE;
        c->d[i] %= BASE;
    }

    if (carry > 0) c->d[c->len - 1] = carry;
    if (a->sign == 0 && b->sign == 0) c->sign = 0;

    remove_preceding_zeroes(c);
    return c;
}

BigInt Subtract(const BigInt a, const BigInt b) {
    BigInt c = new BigIntStruct(1 + max(a->len, b->len));
    long long carry = 0;
    long long temp;

    for (unsigned int i = 0; i < c->len - 1; i++) {
        temp = carry + (i < a->len ? a->d[i] : 0) - (i < b->len ? b->d[i] : 0);
        if (temp < 0) {
            carry = -1;
            c->d[i] = temp + (long long)BASE;
        } else {
            carry = 0;
            c->d[i] = temp;
        }
    }

    if (carry > 0) {
        c->d[c->len - 1] = carry;
    } else if (carry < 0) {
        c->sign = 0;
        carry = 0;
        for (unsigned int i = 0; i < c->len - 1; i++) {
            temp = carry + (i < b->len ? b->d[i] : 0) - (i < a->len ? a->d[i] : 0);
            if (temp < 0) {
                carry = -1;
                c->d[i] = temp + (long long)BASE;
            } else {
                carry = 0;
                c->d[i] = temp;
            }
        }
    }

    remove_preceding_zeroes(c);
    return c;
}

void _MUL_(unsigned long long x, unsigned long long y, unsigned long long &carry, unsigned long long &result) {
    unsigned long long x0 = x % HALFBASE,
                       x1 = x / HALFBASE,
                       y0 = y % HALFBASE,
                       y1 = y / HALFBASE,
                       excess = x1 * y0 + x0 * y1;

    result += x0 * y0 + (excess % HALFBASE) * HALFBASE + carry;
    carry = x1 * y1 + excess / HALFBASE + result / BASE;
    result %= BASE;
}

BigInt Multiply(const BigInt a, const BigInt b) {
    BigInt c = new BigIntStruct(a->len + b->len);
    c->sign = (a->sign == b->sign ? 1 : 0);
    unsigned long long carry;

    for (unsigned int i = 0; i < a->len; i++) {
        carry = 0;
        for (unsigned int j = 0; j < b->len; j++) {
            _MUL_(a->d[i], b->d[j], carry, c->d[i + j]);
        }
        c->d[i + b->len] = carry;
    }

    remove_preceding_zeroes(c);
    return c;
}

void Left_Shift(BigInt num, unsigned int shift) {
    if (shift == 0) return;
    if (num->len == 1 && num->d[0] == 0) return;

    unsigned long long *temp = new unsigned long long[num->len + shift]();
    for (unsigned int i = 0; i < num->len; i++) {
        temp[i + shift] = num->d[i];
    }
    delete[] num->d;
    num->d = temp;
    num->len += shift;
}

int Compare(const BigInt a, const BigInt b) {
    BigInt diff = Subtract(a, b);
    int flag = 0;
    for (unsigned int i = 0; i < diff->len; i++) {
        if (diff->d[i] != 0) flag = 1;
    }
    if (diff->sign == 0) {
        delete diff;
        return -1;
    } else {
        delete diff;
        return flag;
    }
}

BigInt Divide(const BigInt a, const BigInt b, BigInt *remainder) {
    BigInt q = new BigIntStruct(1);
    q->sign = (a->sign == b->sign ? 1 : 0);

    BigInt r = new BigIntStruct(1);
    BigInt ten = new BigIntStruct(1);
    ten->d[0] = 10;

    BigInt table[11];
    table[0] = new BigIntStruct(1);

    for (int i = 1; i <= 10; i++) {
        table[i] = Add(table[i - 1], b);
    }

    unsigned long long mod, cur;
    int quo;
    BigInt temp;

    for (int i = (int)a->len - 1; i >= 0; i--) {
        mod = BASE / 10;
        while (mod) {
            cur = (a->d[i] / mod) % 10;
            mod /= 10;

            temp = r;
            r = Multiply(r, ten);
            delete temp;
            r->d[0] += cur;

            quo = 0;
            while (Compare(r, table[quo]) >= 0) {
                quo++;
            }
            quo--;

            temp = q;
            q = Multiply(q, ten);
            delete temp;
            q->d[0] += quo;

            temp = r;
            r = Subtract(r, table[quo]);
            delete temp;
        }
    }
    remove_preceding_zeroes(r);
    *remainder = r;

    for (int i = 0; i <= 10; i++) delete table[i];
    delete ten;

    remove_preceding_zeroes(q);
    return q;
}

string Decimal_Division(BigInt a, BigInt b) {
    BigInt remainder;
    BigInt temp = new BigIntStruct(1);
    BigInt quotient = Divide(a, b, &remainder);
    unsigned long long mod, cur;
    bool flag = true;
    string result = "";

    for (int i = (int)quotient->len - 1; i >= 0; i--) {
        mod = BASE / 10;
        while (mod) {
            cur = (quotient->d[i] / mod) % 10;
            mod /= 10;
            if (flag) {
                if (cur == 0) continue;
                else flag = false;
            }
            result += to_string(cur);
        }
    }
    
    if(result.empty()) result = "0";
    result += ".";

    Left_Shift(remainder, (decimal_precision + 17) / 18);
    BigInt old_quotient = quotient;
    quotient = Divide(remainder, b, &temp);
    delete old_quotient;

    unsigned int count = 0;
    for (int i = (int)quotient->len - 1; i >= 0 && count < decimal_precision; i--) {
        mod = BASE / 10;
        while (mod && count < decimal_precision) {
            cur = (quotient->d[i] / mod) % 10;
            mod /= 10;
            result += to_string(cur);
            count++;
        }
    }

    delete remainder;
    delete temp;
    delete quotient;

    return result;
}

BigInt Remainder(BigInt a, BigInt b) {
    BigInt r;
    BigInt temp_q = Divide(a, b, &r);
    delete temp_q;
    return r;
}

BigInt Power(BigInt num_val, unsigned long long p) {
    BigInt ans = new BigIntStruct(1);
    ans->d[0] = 1;

    BigInt num = new BigIntStruct(num_val->len);
    for (unsigned int i = 0; i < num->len; i++) num->d[i] = num_val->d[i];

    BigInt temp;
    while (p > 0) {
        if (p & 1) {
            temp = ans;
            ans = Multiply(ans, num);
            delete temp;
        }
        p >>= 1;
        temp = num;
        num = Multiply(num, num);
        delete temp;
    }
    delete num;
    return ans;
}

BigInt GCD(BigInt a_val, BigInt b_val) {
    BigInt a = new BigIntStruct(a_val->len);
    for (unsigned int i = 0; i < a->len; i++) a->d[i] = a_val->d[i];
    BigInt b = new BigIntStruct(b_val->len);
    for (unsigned int i = 0; i < b->len; i++) b->d[i] = b_val->d[i];

    BigInt temp;
    BigInt zero = new BigIntStruct(1);

    while (Compare(b, zero) != 0) {
        temp = Remainder(a, b);
        delete a;
        a = b;
        b = temp;
    }
    delete b;
    delete zero;
    return a;
}

BigInt Factorial(unsigned long long n) {
    BigInt ans = new BigIntStruct(1);
    ans->d[0] = 1;
    for (unsigned long long i = 1; i <= n; i++) {
        BigInt temp_n = new BigIntStruct(1);
        temp_n->d[0] = i;
        BigInt temp_ans = ans;
        ans = Multiply(ans, temp_n);
        delete temp_ans;
        delete temp_n;
    }
    return ans;
}

void precompute_factorial() {
    FACT[0] = Factorial(1);
    BigInt n = new BigIntStruct(1);
    n->d[0] = 1;

    for (int i = 1; i < MAX_FACT; i++) {
        FACT[i] = Multiply(FACT[i - 1], n);
        n->d[0]++;
    }
    delete n;
}

void Increment(const BigInt a, const BigInt delta) {
    if (a->len <= delta->len) {
        increase_size(a, delta->len - a->len + 1);
    }
    unsigned long long carry = 0;
    for (unsigned int i = 0; i < delta->len; i++) {
        a->d[i] += delta->d[i] + carry;
        carry = a->d[i] / BASE;
        a->d[i] %= BASE;
    }
    for (unsigned int i = delta->len; i < a->len; i++) {
        a->d[i] += carry;
        carry = a->d[i] / BASE;
        a->d[i] %= BASE;
    }
}

void increase_size(BigInt b, const unsigned int delta_len) {
    unsigned long long *temp = new unsigned long long[b->len + delta_len]();
    for (unsigned int i = 0; i < b->len; i++) temp[i] = b->d[i];
    delete[] b->d;
    b->d = temp;
    b->len += delta_len;
}

void remove_preceding_zeroes(BigInt a) {
    while (a->len > 1 && a->d[a->len - 1] == 0) {
        a->len--;
    }
}

int isPrime(int n) {
    if (n <= 1) return 0;
    if (n <= 3) return 1;
    if (n % 2 == 0 || n % 3 == 0) return 0;

    for (int i = 5; i * i <= n; i = i + 6)
        if (n % i == 0 || n % (i + 2) == 0)
            return 0;
    return 1;
}

int gcd(int a, int b) {
    while (b) {
        a %= b;
        swap(a, b);
    }
    return a;
}

// ---------------- Complex Functions ----------------

Complex new_Complex() {
    return new ComplexStruct();
}

void print_Complex(Complex a) {
    if (a->imag >= 0)
        cout << a->real << " + " << a->imag << "i\n";
    else
        cout << a->real << " - " << -a->imag << "i\n";
}

long long int real_part(Complex a) { return a->real; }
long long int imag_part(Complex a) { return a->imag; }

Complex conjugate(Complex a) {
    Complex c = new_Complex();
    c->real = a->real;
    c->imag = (a->imag == 0) ? 0 : -a->imag;
    return c;
}

long long int complex_modulus(Complex a) {
    return (a->real * a->real) + (a->imag * a->imag);
}

Complex add_Complex(Complex a, Complex b) {
    Complex c = new_Complex();
    c->real = a->real + b->real;
    c->imag = a->imag + b->imag;
    return c;
}

Complex subtract_Complex(Complex a, Complex b) {
    Complex c = new_Complex();
    c->real = a->real - b->real;
    c->imag = a->imag - b->imag;
    return c;
}

Complex multiply_Complex(Complex a, Complex b) {
    Complex c = new_Complex();
    c->real = (a->real * b->real) - (a->imag * b->imag);
    c->imag = (a->real * b->imag) + (a->imag * b->real);
    return c;
}

Complex divide_Complex(Complex a, Complex b) {
    Complex c = new_Complex();
    Complex conj_b = conjugate(b);
    Complex num = multiply_Complex(a, conj_b);
    long long mod = complex_modulus(b);

    c->real = real_part(num) / mod;
    c->imag = imag_part(num) / mod;

    delete conj_b;
    delete num;
    return c;
}

// ------------ Fraction Functions ------------

Fraction new_Fraction() {
    return new FractionStruct();
}

Fraction input_Fraction() {
    cout << "Enter Numerator: ";
    BigInt a = input_BigInt();
    cout << "Enter Denominator: ";
    BigInt b = input_BigInt();

    Fraction c = new FractionStruct();
    c->num = a;
    c->den = b;
    return c;
}

void print_Fraction(Fraction a) {
    cout << "Numerator :  ";
    print_BigInt(a->num);
    cout << "Denominator : ";
    print_BigInt(a->den);
}

void reduce_Fraction(Fraction a) {
    BigInt g = GCD(a->num, a->den);
    remove_preceding_zeroes(g);
    if (g->len == 1 && g->d[0] == 1) {
        delete g;
        return;
    }
    BigInt rem;
    BigInt new_num = Divide(a->num, g, &rem); delete rem;
    BigInt new_den = Divide(a->den, g, &rem); delete rem;

    delete a->num;
    delete a->den;
    a->num = new_num;
    a->den = new_den;
    delete g;
}

Fraction add_Fraction(Fraction a, Fraction b) {
    Fraction c = new_Fraction();
    BigInt num1 = Multiply(a->num, b->den);
    BigInt num2 = Multiply(a->den, b->num);
    c->num = Add(num1, num2);
    c->den = Multiply(a->den, b->den);
    delete num1;
    delete num2;
    return c;
}

Fraction subtract_Fraction(Fraction a, Fraction b) {
    Fraction c = new_Fraction();
    BigInt num1 = Multiply(a->num, b->den);
    BigInt num2 = Multiply(a->den, b->num);
    c->num = Subtract(num1, num2);
    c->den = Multiply(a->den, b->den);
    delete num1;
    delete num2;
    return c;
}

Fraction multiply_Fraction(Fraction a, Fraction b) {
    Fraction c = new_Fraction();
    c->num = Multiply(a->num, b->num);
    c->den = Multiply(a->den, b->den);
    return c;
}

Fraction divide_Fraction(Fraction a, Fraction b) {
    Fraction c = new_Fraction();
    c->num = Multiply(a->num, b->den);
    c->den = Multiply(a->den, b->num);
    return c;
}

void reciprocal_Fraction(Fraction a) {
    BigInt temp = a->num;
    a->num = a->den;
    a->den = temp;
}

void free_Fraction(Fraction a) {
    if (a->num) delete a->num;
    if (a->den) delete a->den;
    delete a;
}

void cancel_zeroes(Fraction a) {
    unsigned int cnt = 0;
    for (unsigned int i = 0; i < min(a->num->len, a->den->len); i++) {
        if (a->num->d[i] == 0 && a->den->d[i] == 0) cnt++;
        else break;
    }
    if (cnt == 0) return;

    for (unsigned int i = 0; i < a->num->len - cnt; i++) a->num->d[i] = a->num->d[i + cnt];
    for (unsigned int i = 0; i < a->den->len - cnt; i++) a->den->d[i] = a->den->d[i + cnt];

    a->num->len -= cnt;
    a->den->len -= cnt;
}

Fraction Square_Root(BigInt k, int n) {
    Fraction x = new_Fraction();
    int flag = 0;

    if (k->len == 1 && k->d[0] == 10005) {
        flag = 1;
        x->num = new BigIntStruct(4);
        x->num->d[0] = 38194350081024001ULL;
        x->num->d[1] = 947199942084943826ULL;
        x->num->d[2] = 764652037898659122ULL;
        x->num->d[3] = 141301459ULL;

        x->den = new BigIntStruct(4);
        x->den->d[0] = 118368174297600640ULL;
        x->den->d[1] = 1550394278198635ULL;
        x->den->d[2] = 476412055532869542ULL;
        x->den->d[3] = 1412661ULL;
    } else {
        x->num = new BigIntStruct(1);
        x->num->d[0] = 2;
        x->den = new BigIntStruct(1);
        x->den->d[0] = 1;
    }

    Fraction f, df, temp_f;
    Fraction two = new_Fraction();
    two->num = new BigIntStruct(1);
    two->den = new BigIntStruct(1);
    two->num->d[0] = 2;
    two->den->d[0] = 1;

    Fraction nn = new_Fraction();
    nn->den = new BigIntStruct(1);
    nn->num = k;
    nn->den->d[0] = 1;

    if (flag) printf("Computing term:    ");

    for (int i = 0; i < n; i++) {
        if (flag) printf("\b\b\b%3d", i);
        f = multiply_Fraction(x, x);
        temp_f = f;
        f = subtract_Fraction(f, nn);
        free_Fraction(temp_f);
        
        df = multiply_Fraction(x, two);
        Fraction temp_div = divide_Fraction(f, df);
        Fraction temp_x = x;
        
        x = subtract_Fraction(x, temp_div);

        free_Fraction(df);
        free_Fraction(f);
        free_Fraction(temp_div);
        if(temp_x != x) free_Fraction(temp_x);

        cancel_zeroes(x);
        reduce_Fraction(x);
    }
    
    if (flag) {
        printf("... Done!\nRoot 10005 calculated!\n");
    }
    
    delete two->num; delete two->den; delete two;
    delete nn->den; delete nn;

    return x;
}

void PI_Chudnovsky(int n) {
    long long k = -6;

    BigInt c = new BigIntStruct(1);
    BigInt p = new BigIntStruct(1);
    BigInt q = new BigIntStruct(1);
    BigInt L = new BigIntStruct(1);
    BigInt dL = new BigIntStruct(1);
    BigInt X = new BigIntStruct(1);
    BigInt dX = new BigIntStruct(1);
    Fraction M = new_Fraction();
    M->num = new BigIntStruct(1);
    M->den = new BigIntStruct(1);

    c->d[0] = 426880;
    L->d[0] = 13591409;
    dL->d[0] = 545140134;
    X->d[0] = 1;
    dX->d[0] = 262537412640768000ULL;
    M->num->d[0] = 1;
    M->den->d[0] = 1;

    Fraction T = new_Fraction();
    Fraction SUM0 = new_Fraction();
    Fraction SUM1 = new_Fraction();
    SUM0->num = new BigIntStruct(1);
    SUM0->den = new BigIntStruct(1);
    SUM1->num = new BigIntStruct(1);
    SUM1->den = new BigIntStruct(1);

    T->num = L;
    T->den = X;
    Fraction temp_T = T;
    T = multiply_Fraction(T, M);
    delete temp_T;
    
    SUM0->num = new BigIntStruct(1);
    SUM0->num->d[0] = L->d[0];
    SUM0->den = new BigIntStruct(1);
    SUM0->den->d[0] = X->d[0];
    
    SUM1->num->d[0] = 0;
    SUM1->den->d[0] = 1;

    if (sqrt_10005 == nullptr) {
        cout << "Chudnovsky formula requires square root of 10005 to be calculated first.\n";
        cout << "Computing sqrt(10005)...\n";
        BigInt _10005 = new BigIntStruct(1);
        _10005->d[0] = 10005;
        sqrt_10005 = Square_Root(_10005, 4);
        cout << "sqrt(10005) computed\n";
    }

    printf("Computing term    ");

    for (int i = 1; i <= n; i++) {
        printf("\b\b\b%3d", i);
        k += 12;
        p->d[0] = k * k * k - 16 * k;
        q->d[0] = i * i * i;

        BigInt old_m_num = M->num;
        BigInt old_m_den = M->den;
        M->num = Multiply(M->num, p);
        M->den = Multiply(M->den, q);
        delete old_m_num; delete old_m_den;

        BigInt old_L = L;
        L = Add(L, dL);
        delete old_L;

        BigInt old_X = X;
        X = Multiply(X, dX);
        delete old_X;

        Fraction temp_T2 = new_Fraction();
        temp_T2->num = L;
        temp_T2->den = X;
        
        Fraction old_T = T;
        T = multiply_Fraction(temp_T2, M);
        free_Fraction(old_T);
        delete temp_T2;

        if (i % 2 == 0) {
            Fraction old_sum0 = SUM0;
            SUM0 = add_Fraction(SUM0, T);
            cancel_zeroes(SUM0);
            free_Fraction(old_sum0);
        } else {
            Fraction old_sum1 = SUM1;
            SUM1 = add_Fraction(SUM1, T);
            cancel_zeroes(SUM1);
            free_Fraction(old_sum1);
        }

        cancel_zeroes(M);
    }

    cout << "... Done!\nCalculating SUM of terms...\n";

    Fraction SUM = subtract_Fraction(SUM0, SUM1);

    cout << "SUM of terms calculated\n";

    reciprocal_Fraction(SUM);
    cancel_zeroes(SUM);

    PI_val = multiply_Fraction(SUM, sqrt_10005);
    BigInt old_pi_num = PI_val->num;
    PI_val->num = Multiply(PI_val->num, c);
    delete old_pi_num;

    cancel_zeroes(PI_val);
    
    // Cleanup internal references
    delete p; delete q; delete dL; delete dX;
    free_Fraction(M); free_Fraction(T); free_Fraction(SUM0); free_Fraction(SUM1); free_Fraction(SUM);
}

int main() {
    int choice;
    clock_t t;
    double time_taken;

    while (true) {
        cout << "===============================================================\n";
        cout << "(I)\tBasic Operations on Big Integers\n";
        cout << "   \t--------------------------------\n";
        cout << "\t  1. Addition\n";
        cout << "\t  2. Subtraction\n";
        cout << "\t  3. Multiplication\n";
        cout << "\t  4. Division\n";
        cout << "\t  5. Decimal Division\n";
        cout << "\t  6. Remainder (Modulo)\n";
        cout << "\t  7. GCD\n";
        cout << "\t  8. Power\n";
        cout << "\t  9. Factorial\n\n";
        cout << "(II)\tOperations on Complex Numbers\n";
        cout << "   \t------------------------------\n";
        cout << "\t 10. Addition\n";
        cout << "\t 11. Subtraction\n";
        cout << "\t 12. Multiplication\n";
        cout << "\t 13. Division\n";
        cout << "\t 14. Conjugate\n\n";
        cout << "(III)\tOperations on Fractions\n";
        cout << "   \t------------------------\n";
        cout << "\t 15. Addition\n";
        cout << "\t 16. Subtraction\n";
        cout << "\t 17. Multiplication\n";
        cout << "\t 18. Division\n";
        cout << "\t 19. Reduce to Simplest Form\n\n";
        cout << "(IV)\tCOMPUTATION OF PI\n";
        cout << "   \t-----------------\n";
        cout << "\t 20. Compute Sqrt(10005) using Newton-Raphson Algorithm\n";
        cout << "\t 21. Compute Value of PI using Chudnovsky Algorithm\n\n";
        cout << "(V)\tMiscellaneous\n";
        cout << "   \t-------------\n";
        cout << "\t 22. Set Decimal Precision\n";
        cout << "\t 23. Exit the program\n";
        cout << "===============================================================\n\n";

        cout << "Enter your choice: ";
        cin >> choice;

        switch (choice) {
            case 1: {
                cout << "Enter the first number: ";
                BigInt a = input_BigInt();
                cout << "Enter the second number: ";
                BigInt b = input_BigInt();
                t = clock();
                BigInt c = Add(a, b);
                cout << "The sum is: ";
                print_BigInt(c);
                t = clock() - t;
                time_taken = ((double)t) / CLOCKS_PER_SEC;
                cout << "Execution time: " << time_taken << " seconds\n\n";
                delete a; delete b; delete c;
                break;
            }
            case 2: {
                cout << "Enter the first number: ";
                BigInt a = input_BigInt();
                cout << "Enter the second number: ";
                BigInt b = input_BigInt();
                t = clock();
                BigInt c = Subtract(a, b);
                cout << "The difference is: ";
                print_BigInt(c);
                t = clock() - t;
                time_taken = ((double)t) / CLOCKS_PER_SEC;
                cout << "Execution time: " << time_taken << " seconds\n\n";
                delete a; delete b; delete c;
                break;
            }
            case 3: {
                cout << "Enter the first number: ";
                BigInt a = input_BigInt();
                cout << "Enter the second number: ";
                BigInt b = input_BigInt();
                t = clock();
                BigInt c = Multiply(a, b);
                t = clock() - t;
                time_taken = ((double)t) / CLOCKS_PER_SEC;
                cout << "The product is: ";
                print_BigInt(c);
                cout << "Execution time: " << time_taken << " seconds\n\n";
                delete a; delete b; delete c;
                break;
            }
            case 4: {
                cout << "Enter the dividend: ";
                BigInt a = input_BigInt();
                cout << "Enter the divisor: ";
                BigInt b = input_BigInt();
                BigInt rem;
                t = clock();
                BigInt c = Divide(a, b, &rem);
                t = clock() - t;
                time_taken = ((double)t) / CLOCKS_PER_SEC;
                cout << "The quotient is: ";
                print_BigInt(c);
                cout << "The remainder is: ";
                print_BigInt(rem);
                cout << "Execution time: " << time_taken << " seconds\n\n";
                delete a; delete b; delete c; delete rem;
                break;
            }
            case 5: {
                cout << "Enter the dividend: ";
                BigInt a = input_BigInt();
                cout << "Enter the divisor: ";
                BigInt b = input_BigInt();
                t = clock();
                string c = Decimal_Division(a, b);
                t = clock() - t;
                time_taken = ((double)t) / CLOCKS_PER_SEC;
                cout << "The quotient is: \n" << c << "\n";
                cout << "Execution time: " << time_taken << " seconds\n\n";
                delete a; delete b;
                break;
            }
            case 6: {
                cout << "Enter the dividend: ";
                BigInt a = input_BigInt();
                cout << "Enter the divisor: ";
                BigInt b = input_BigInt();
                BigInt rem;
                t = clock();
                BigInt c = Divide(a, b, &rem);
                t = clock() - t;
                time_taken = ((double)t) / CLOCKS_PER_SEC;
                cout << "The remainder is: ";
                print_BigInt(rem);
                cout << "Execution time: " << time_taken << " seconds\n\n";
                delete a; delete b; delete c; delete rem;
                break;
            }
            case 7: {
                cout << "Enter the first number: ";
                BigInt a = input_BigInt();
                cout << "Enter the second number: ";
                BigInt b = input_BigInt();
                t = clock();
                BigInt c = GCD(a, b);
                t = clock() - t;
                time_taken = ((double)t) / CLOCKS_PER_SEC;
                cout << "The GCD is: ";
                print_BigInt(c);
                cout << "Execution time: " << time_taken << " seconds\n\n";
                delete a; delete b; delete c;
                break;
            }
            case 8: {
                cout << "Enter the base: ";
                BigInt a = input_BigInt();
                cout << "Enter the exponent: ";
                unsigned long long b;
                cin >> b;
                t = clock();
                BigInt c = Power(a, b);
                t = clock() - t;
                time_taken = ((double)t) / CLOCKS_PER_SEC;
                cout << "The result is: ";
                print_BigInt(c);
                cout << "Execution time: " << time_taken << " seconds\n\n";
                delete a; delete c;
                break;
            }
            case 9: {
                cout << "Enter the number: ";
                unsigned long long a;
                cin >> a;
                t = clock();
                BigInt c = Factorial(a);
                t = clock() - t;
                time_taken = ((double)t) / CLOCKS_PER_SEC;
                cout << "The factorial is: ";
                print_BigInt(c);
                cout << "Execution time: " << time_taken << " seconds\n\n";
                delete c;
                break;
            }
            case 10: {
                long long int a1, a2, b1, b2;
                cout << "Enter real part of first number: "; cin >> a1;
                cout << "Enter imaginary part of first number: "; cin >> a2;
                cout << "Enter real part of second number: "; cin >> b1;
                cout << "Enter imaginary part of second number: "; cin >> b2;
                Complex a = new_Complex(); a->real = a1; a->imag = a2;
                Complex b = new_Complex(); b->real = b1; b->imag = b2;
                t = clock();
                Complex c = add_Complex(a, b);
                t = clock() - t;
                time_taken = ((double)t) / CLOCKS_PER_SEC;
                cout << "The sum is: "; print_Complex(c);
                cout << "Execution time: " << time_taken << " seconds\n\n";
                delete a; delete b; delete c;
                break;
            }
            case 11: {
                long long int a1, a2, b1, b2;
                cout << "Enter real part of first number: "; cin >> a1;
                cout << "Enter imaginary part of first number: "; cin >> a2;
                cout << "Enter real part of second number: "; cin >> b1;
                cout << "Enter imaginary part of second number: "; cin >> b2;
                Complex a = new_Complex(); a->real = a1; a->imag = a2;
                Complex b = new_Complex(); b->real = b1; b->imag = b2;
                t = clock();
                Complex c = subtract_Complex(a, b);
                t = clock() - t;
                time_taken = ((double)t) / CLOCKS_PER_SEC;
                cout << "The difference is: "; print_Complex(c);
                cout << "Execution time: " << time_taken << " seconds\n\n";
                delete a; delete b; delete c;
                break;
            }
            case 12: {
                long long int a1, a2, b1, b2;
                cout << "Enter real part of first number: "; cin >> a1;
                cout << "Enter imaginary part of first number: "; cin >> a2;
                cout << "Enter real part of second number: "; cin >> b1;
                cout << "Enter imaginary part of second number: "; cin >> b2;
                Complex a = new_Complex(); a->real = a1; a->imag = a2;
                Complex b = new_Complex(); b->real = b1; b->imag = b2;
                t = clock();
                Complex c = multiply_Complex(a, b);
                t = clock() - t;
                time_taken = ((double)t) / CLOCKS_PER_SEC;
                cout << "The product is: "; print_Complex(c);
                cout << "Execution time: " << time_taken << " seconds\n\n";
                delete a; delete b; delete c;
                break;
            }
            case 13: {
                long long int a1, a2, b1, b2;
                cout << "Enter real part of first number: "; cin >> a1;
                cout << "Enter imaginary part of first number: "; cin >> a2;
                cout << "Enter real part of second number: "; cin >> b1;
                cout << "Enter imaginary part of second number: "; cin >> b2;
                Complex a = new_Complex(); a->real = a1; a->imag = a2;
                Complex b = new_Complex(); b->real = b1; b->imag = b2;
                t = clock();
                Complex c = divide_Complex(a, b);
                t = clock() - t;
                time_taken = ((double)t) / CLOCKS_PER_SEC;
                cout << "The quotient is: "; print_Complex(c);
                cout << "Execution time: " << time_taken << " seconds\n\n";
                delete a; delete b; delete c;
                break;
            }
            case 14: {
                long long int a1, a2;
                cout << "Enter real part of the number: "; cin >> a1;
                cout << "Enter imaginary part of the number: "; cin >> a2;
                Complex a = new_Complex(); a->real = a1; a->imag = a2;
                t = clock();
                Complex c = conjugate(a);
                t = clock() - t;
                time_taken = ((double)t) / CLOCKS_PER_SEC;
                cout << "The conjugate is: "; print_Complex(c);
                cout << "Execution time: " << time_taken << " seconds\n\n";
                delete a; delete c;
                break;
            }
            case 15: {
                cout << "For first number:\n"; Fraction a = input_Fraction();
                cout << "For second number:\n"; Fraction b = input_Fraction();
                t = clock();
                Fraction c = add_Fraction(a, b);
                reduce_Fraction(c);
                t = clock() - t;
                time_taken = ((double)t) / CLOCKS_PER_SEC;
                cout << "The sum is:\n"; print_Fraction(c);
                cout << "Execution time: " << time_taken << " seconds\n\n";
                free_Fraction(a); free_Fraction(b); free_Fraction(c);
                break;
            }
            case 16: {
                cout << "For first number:\n"; Fraction a = input_Fraction();
                cout << "For second number:\n"; Fraction b = input_Fraction();
                t = clock();
                Fraction c = subtract_Fraction(a, b);
                reduce_Fraction(c);
                t = clock() - t;
                time_taken = ((double)t) / CLOCKS_PER_SEC;
                cout << "The difference is:\n"; print_Fraction(c);
                cout << "Execution time: " << time_taken << " seconds\n\n";
                free_Fraction(a); free_Fraction(b); free_Fraction(c);
                break;
            }
            case 17: {
                cout << "For first number:\n"; Fraction a = input_Fraction();
                cout << "For second number:\n"; Fraction b = input_Fraction();
                t = clock();
                Fraction c = multiply_Fraction(a, b);
                reduce_Fraction(c);
                t = clock() - t;
                time_taken = ((double)t) / CLOCKS_PER_SEC;
                cout << "The product is:\n"; print_Fraction(c);
                cout << "Execution time: " << time_taken << " seconds\n\n";
                free_Fraction(a); free_Fraction(b); free_Fraction(c);
                break;
            }
            case 18: {
                cout << "For first number:\n"; Fraction a = input_Fraction();
                cout << "For second number:\n"; Fraction b = input_Fraction();
                t = clock();
                Fraction c = divide_Fraction(a, b);
                reduce_Fraction(c);
                t = clock() - t;
                time_taken = ((double)t) / CLOCKS_PER_SEC;
                cout << "The quotient is:\n"; print_Fraction(c);
                cout << "Execution time: " << time_taken << " seconds\n\n";
                free_Fraction(a); free_Fraction(b); free_Fraction(c);
                break;
            }
            case 19: {
                Fraction a = input_Fraction();
                t = clock();
                reduce_Fraction(a);
                t = clock() - t;
                time_taken = ((double)t) / CLOCKS_PER_SEC;
                cout << "Your Fraction in simplest form:\n";
                print_Fraction(a);
                cout << "Execution time: " << time_taken << " seconds\n\n";
                free_Fraction(a);
                break;
            }
            case 20: {
                BigInt a = new BigIntStruct(1);
                a->d[0] = 10005;
                int n;
                cout << "Enter number of terms of Newton-Raphson Algorithm: ";
                cin >> n;
                cout << "Computing sqrt(10005)...\n";
                t = clock();
                if(sqrt_10005 != nullptr) { free_Fraction(sqrt_10005); }
                sqrt_10005 = Square_Root(a, n);
                t = clock() - t;
                time_taken = ((double)t) / CLOCKS_PER_SEC;
                cout << "Rational Equivalent of square root computed\n";
                print_Fraction(sqrt_10005);
                cout << "Execution time: " << time_taken << " seconds\n";
                cout << "Do you want to convert it to decimal and write it to a file?\n";
                cout << "Your choice? (y/n): ";
                char ch;
                cin >> ch;
                if (tolower(ch) == 'y') {
                    ofstream fp(OUTPUT_SQRT_FILENAME);
                    if (!fp.is_open()) {
                        cout << "Error opening file\n";
                        break;
                    }
                    t = clock();
                    string ans = Decimal_Division(sqrt_10005->num, sqrt_10005->den);
                    t = clock() - t;
                    time_taken = ((double)t) / CLOCKS_PER_SEC;
                    fp << ans;
                    fp.close();
                    cout << "Sqrt(10005) =\n" << ans << "\n";
                    cout << "Execution time: " << time_taken << " seconds\n";
                    cout << "Output Written to file\n";
                }
                cout << "\n";
                delete a;
                break;
            }
            case 21: {
                int n;
                cout << "Enter number of terms of Chudnovsky Algorithm: ";
                cin >> n;
                cout << "Computing pi...\n";
                t = clock();
                if(PI_val != nullptr) { free_Fraction(PI_val); }
                PI_Chudnovsky(n);
                t = clock() - t;
                time_taken = ((double)t) / CLOCKS_PER_SEC;
                cout << "Rational Equivalent of pi computed\n";
                cout << "Execution time: " << time_taken << " seconds\n";
                cout << "Do you want to convert it to decimal and write it to a file?\n";
                cout << "Your choice? (y/n): ";
                char ch;
                cin >> ch;
                if (tolower(ch) == 'y') {
                    ofstream fp(OUTPUT_PI_FILENAME);
                    if (!fp.is_open()) {
                        cout << "Error opening file\n";
                        break;
                    }
                    t = clock();
                    PI_str = Decimal_Division(PI_val->num, PI_val->den);
                    t = clock() - t;
                    time_taken = ((double)t) / CLOCKS_PER_SEC;
                    fp << PI_str;
                    fp.close();
                    cout << "PI =\n" << PI_str << "\n";
                    cout << "Execution time: " << time_taken << " seconds\n";
                    cout << "Output Written to file\n";
                }
                cout << "\n";
                break;
            }
            case 22: {
                cout << "Enter new precision for decimal conversion: ";
                cin >> decimal_precision;
                cout << "\n";
                break;
            }
            case 23: {
                cout << "Exiting...\n";
                if(sqrt_10005 != nullptr) free_Fraction(sqrt_10005);
                if(PI_val != nullptr) free_Fraction(PI_val);
                return 0;
            }
            default: {
                cout << "Invalid choice, please enter a correct choice\n\n";
                break;
            }
        }
    }
    return 0;
}