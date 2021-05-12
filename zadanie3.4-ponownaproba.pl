dodawanie_do_bazy :-
write('Dodawanie studenta do bazy. Podaj dane.'),nl,
write('Wpisz imie'),nl,
read(imie),nl;
write('Wpisz nazwisko'),nl,
read(nazwisko),nl;
write('Wpisz numer indeksu'),nl,
read(numer_indeksu),nl;
asserta(student(imie,nazwisko,numer_indeksu)).
